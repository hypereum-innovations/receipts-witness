// SPDX-License-Identifier: Apache-2.0
//
// receipts-witness — Standalone RFC 9162 & C2SP tlog-witness binary.
// Verifies SHA-256 Merkle consistency proofs, enforces anti-rollback and
// split-view equivocation resistance with atomic disk persistence, and emits
// C2SP tlog-cosignature/v1 Ed25519 cosignatures.
package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"
)

const (
	NoteKeyEd25519     byte = 0x01
	NoteKeyCosignature byte = 0x04
)

// LeafHash computes RFC 9162 §2.1 leaf hash: SHA-256(0x00 || data).
func LeafHash(data []byte) []byte {
	h := sha256.New()
	h.Write([]byte{0x00})
	h.Write(data)
	return h.Sum(nil)
}

// NodeHash computes RFC 9162 §2.1 interior node hash: SHA-256(0x01 || left || right).
func NodeHash(left, right []byte) []byte {
	h := sha256.New()
	h.Write([]byte{0x01})
	h.Write(left)
	h.Write(right)
	return h.Sum(nil)
}

func largestPow2LessThan(n int64) int64 {
	var k int64 = 1
	for k*2 < n {
		k *= 2
	}
	return k
}

// MerkleTreeHash computes the RFC 9162 Merkle Tree Hash (MTH) over pre-hashed leaves.
func MerkleTreeHash(leaves [][]byte) []byte {
	n := int64(len(leaves))
	if n == 0 {
		sum := sha256.Sum256(nil)
		return sum[:]
	}
	if n == 1 {
		out := make([]byte, len(leaves[0]))
		copy(out, leaves[0])
		return out
	}
	k := largestPow2LessThan(n)
	return NodeHash(MerkleTreeHash(leaves[:k]), MerkleTreeHash(leaves[k:]))
}

func subproof(m int64, leaves [][]byte, complete bool) [][]byte {
	n := int64(len(leaves))
	if m == n {
		if complete {
			return nil
		}
		return [][]byte{MerkleTreeHash(leaves)}
	}
	k := largestPow2LessThan(n)
	if m <= k {
		return append(subproof(m, leaves[:k], complete), MerkleTreeHash(leaves[k:]))
	}
	return append(subproof(m-k, leaves[k:], false), MerkleTreeHash(leaves[:k]))
}

// BuildConsistencyProof generates an RFC 9162 consistency proof from firstSize to len(leaves).
func BuildConsistencyProof(firstSize int64, leaves [][]byte) ([][]byte, error) {
	n := int64(len(leaves))
	if firstSize < 1 || firstSize > n {
		return nil, fmt.Errorf("consistency size %d out of range [1, %d]", firstSize, n)
	}
	if firstSize == n {
		return [][]byte{}, nil
	}
	return subproof(firstSize, leaves, true), nil
}

// VerifyConsistency implements RFC 9162 §2.1.4.2 consistency proof verification.
func VerifyConsistency(firstSize, secondSize int64, proof [][]byte, firstRoot, secondRoot []byte) bool {
	if len(firstRoot) != 32 || len(secondRoot) != 32 {
		return false
	}
	if firstSize == secondSize {
		return len(proof) == 0 && bytes.Equal(firstRoot, secondRoot)
	}
	if firstSize < 1 || firstSize >= secondSize {
		return false
	}
	for _, h := range proof {
		if len(h) != 32 {
			return false
		}
	}

	hashes := make([][]byte, 0, len(proof)+1)
	if (firstSize & (firstSize - 1)) == 0 {
		hashes = append(hashes, firstRoot)
	}
	hashes = append(hashes, proof...)
	if len(hashes) == 0 {
		return false
	}

	fn := firstSize - 1
	sn := secondSize - 1
	for fn%2 == 1 {
		fn >>= 1
		sn >>= 1
	}

	fr := hashes[0]
	sr := hashes[0]
	for _, c := range hashes[1:] {
		if sn == 0 {
			return false
		}
		if fn%2 == 1 || fn == sn {
			fr = NodeHash(c, fr)
			sr = NodeHash(c, sr)
			for fn%2 == 0 && fn != 0 {
				fn >>= 1
				sn >>= 1
			}
		} else {
			sr = NodeHash(sr, c)
		}
		fn >>= 1
		sn >>= 1
	}
	return bytes.Equal(fr, firstRoot) && bytes.Equal(sr, secondRoot) && sn == 0
}

// NoteKeyID computes the 4-byte C2SP signed-note key identifier.
func NoteKeyID(name string, keyType byte, pubKey []byte) []byte {
	h := sha256.New()
	h.Write([]byte(name))
	h.Write([]byte{0x0a, keyType})
	h.Write(pubKey)
	sum := h.Sum(nil)
	return sum[:4]
}

// NoteVerifierString returns "<name>+<8-hex-keyid>+<base64(keyType||rawPub)>".
func NoteVerifierString(name string, keyType byte, pubKey ed25519.PublicKey) string {
	kid := NoteKeyID(name, keyType, pubKey)
	raw := append([]byte{keyType}, pubKey...)
	return fmt.Sprintf("%s+%s+%s", name, hex.EncodeToString(kid), base64.StdEncoding.EncodeToString(raw))
}

// ParsedVerifier holds a parsed C2SP note verifier key.
type ParsedVerifier struct {
	Name      string
	KeyID     []byte
	KeyType   byte
	PublicKey ed25519.PublicKey
}

// ParseNoteVerifierString parses a C2SP note verifier string.
func ParseNoteVerifierString(v string) (*ParsedVerifier, error) {
	first := strings.IndexByte(v, '+')
	if first <= 0 {
		return nil, errors.New("malformed note verifier string: missing first '+'")
	}
	second := strings.IndexByte(v[first+1:], '+')
	if second <= 0 {
		return nil, errors.New("malformed note verifier string: missing second '+'")
	}
	second += first + 1
	name := v[:first]
	kidHex := v[first+1 : second]
	keyB64 := v[second+1:]
	kid, err := hex.DecodeString(kidHex)
	if err != nil || len(kid) != 4 {
		return nil, errors.New("malformed note verifier key id")
	}
	keyBytes, err := base64.StdEncoding.DecodeString(keyB64)
	if err != nil || len(keyBytes) != 1+ed25519.PublicKeySize {
		return nil, errors.New("malformed note verifier public key")
	}
	expectedKid := NoteKeyID(name, keyBytes[0], keyBytes[1:])
	if !bytes.Equal(kid, expectedKid) {
		return nil, errors.New("note verifier key id mismatch")
	}
	return &ParsedVerifier{
		Name:      name,
		KeyID:     kid,
		KeyType:   keyBytes[0],
		PublicKey: ed25519.PublicKey(keyBytes[1:]),
	}, nil
}

// NoteSignature represents a parsed signature line on a C2SP signed note.
type NoteSignature struct {
	Name      string
	KeyID     []byte
	Signature []byte
}

// Checkpoint represents a parsed C2SP tlog-checkpoint.
type Checkpoint struct {
	Origin     string
	TreeSize   int64
	Root       []byte
	Body       string
	Signatures []NoteSignature
}

// ParseCheckpoint parses a C2SP signed-note checkpoint.
func ParseCheckpoint(text string) (*Checkpoint, error) {
	sep := strings.Index(text, "\n\n")
	if sep < 0 {
		return nil, errors.New("checkpoint has no signature block separator")
	}
	body := text[:sep+1]
	sigBlock := text[sep+2:]
	lines := strings.Split(strings.TrimSuffix(body, "\n"), "\n")
	if len(lines) < 3 {
		return nil, errors.New("checkpoint body requires at least 3 lines")
	}
	origin := strings.TrimSpace(lines[0])
	if origin == "" {
		return nil, errors.New("checkpoint origin is empty")
	}
	treeSize, err := strconv.ParseInt(lines[1], 10, 64)
	if err != nil || treeSize < 0 {
		return nil, errors.New("invalid checkpoint tree size")
	}
	root, err := base64.StdEncoding.DecodeString(lines[2])
	if err != nil || len(root) != 32 {
		return nil, errors.New("invalid checkpoint root hash")
	}

	var sigs []NoteSignature
	for _, line := range strings.Split(sigBlock, "\n") {
		if line == "" {
			continue
		}
		if !strings.HasPrefix(line, "— ") {
			return nil, errors.New("malformed signature line prefix")
		}
		rest := line[len("— "):]
		sp := strings.IndexByte(rest, ' ')
		if sp <= 0 {
			return nil, errors.New("malformed signature line")
		}
		raw, err := base64.StdEncoding.DecodeString(rest[sp+1:])
		if err != nil || len(raw) < 5 {
			return nil, errors.New("signature too short")
		}
		sigs = append(sigs, NoteSignature{
			Name:      rest[:sp],
			KeyID:     raw[:4],
			Signature: raw[4:],
		})
	}
	if len(sigs) == 0 {
		return nil, errors.New("checkpoint contains no signatures")
	}
	return &Checkpoint{
		Origin:     origin,
		TreeSize:   treeSize,
		Root:       root,
		Body:       body,
		Signatures: sigs,
	}, nil
}

// FormatCheckpoint creates and signs a C2SP checkpoint for a transparency log.
func FormatCheckpoint(origin string, treeSize int64, root []byte, logName string, logPriv ed25519.PrivateKey) (string, error) {
	if len(root) != 32 {
		return "", errors.New("root must be 32 bytes")
	}
	if logName == "" {
		logName = origin
	}
	body := fmt.Sprintf("%s\n%d\n%s\n", origin, treeSize, base64.StdEncoding.EncodeToString(root))
	pub := logPriv.Public().(ed25519.PublicKey)
	kid := NoteKeyID(logName, NoteKeyEd25519, pub)
	sig := ed25519.Sign(logPriv, []byte(body))
	payload := append(append([]byte{}, kid...), sig...)
	sigLine := fmt.Sprintf("— %s %s\n", logName, base64.StdEncoding.EncodeToString(payload))
	return body + "\n" + sigLine, nil
}

// CosignCheckpoint generates a C2SP tlog-cosignature/v1 Ed25519 cosignature over a checkpoint.
// Returns the standalone signature line ("— <name> <base64>\n") and the full cosigned checkpoint text.
func CosignCheckpoint(checkpointText, witnessName string, priv ed25519.PrivateKey, timestampSec uint64) (string, string, error) {
	cp, err := ParseCheckpoint(checkpointText)
	if err != nil {
		return "", "", err
	}
	var tsBytes [8]byte
	binary.BigEndian.PutUint64(tsBytes[:], timestampSec)
	msg := fmt.Sprintf("cosignature/v1\ntime %d\n%s", timestampSec, cp.Body)
	sig := ed25519.Sign(priv, []byte(msg))

	pub := priv.Public().(ed25519.PublicKey)
	kid := NoteKeyID(witnessName, NoteKeyCosignature, pub)

	raw := make([]byte, 0, 4+8+ed25519.SignatureSize)
	raw = append(raw, kid...)
	raw = append(raw, tsBytes[:]...)
	raw = append(raw, sig...)

	sigLine := fmt.Sprintf("— %s %s\n", witnessName, base64.StdEncoding.EncodeToString(raw))
	full := checkpointText
	if !strings.HasSuffix(full, "\n") {
		full += "\n"
	}
	full += sigLine
	return sigLine, full, nil
}

// VerifyCosignature verifies a witness cosignature on a checkpoint against a witness verifier string.
func VerifyCosignature(checkpointText, witnessVerifier string) (uint64, bool, error) {
	cp, err := ParseCheckpoint(checkpointText)
	if err != nil {
		return 0, false, err
	}
	v, err := ParseNoteVerifierString(witnessVerifier)
	if err != nil {
		return 0, false, err
	}
	if v.KeyType != NoteKeyCosignature {
		return 0, false, errors.New("verifier key is not a witness cosignature key (0x04)")
	}
	for _, s := range cp.Signatures {
		if s.Name == v.Name && bytes.Equal(s.KeyID, v.KeyID) {
			if len(s.Signature) != 8+ed25519.SignatureSize {
				return 0, false, nil
			}
			ts := binary.BigEndian.Uint64(s.Signature[:8])
			msg := fmt.Sprintf("cosignature/v1\ntime %d\n%s", ts, cp.Body)
			if ed25519.Verify(v.PublicKey, []byte(msg), s.Signature[8:]) {
				return ts, true, nil
			}
		}
	}
	return 0, false, nil
}

// OriginState tracks the latest verified (TreeSize, Root) for a log origin.
type OriginState struct {
	Origin     string `json:"origin"`
	TreeSize   int64  `json:"tree_size"`
	RootBase64 string `json:"root_base64"`
	UpdatedAt  int64  `json:"updated_at"`
}

// WitnessError represents a structured HTTP error from the witness.
type WitnessError struct {
	StatusCode int
	Code       string
	Message    string
}

func (e *WitnessError) Error() string {
	return fmt.Sprintf("%s: %s", e.Code, e.Message)
}

// DefaultWitnessOperatorLabel is the launch witness operator disclosure label [OWNER].
const DefaultWitnessOperatorLabel = "operated by Hypereum"

// WitnessEngine manages anti-rollback state and cosigning.
type WitnessEngine struct {
	mu           sync.Mutex
	Name         string
	Operator     string
	PrivKey      ed25519.PrivateKey
	PubKey       ed25519.PublicKey
	StateFile    string
	NowUnix      func() uint64
	LogVerifiers map[string]*ParsedVerifier
	state        map[string]OriginState
}

// NewWitnessEngine initializes a WitnessEngine, loading persisted state if stateFile exists.
func NewWitnessEngine(name string, priv ed25519.PrivateKey, stateFile string, logVerifierStrings []string) (*WitnessEngine, error) {
	if name == "" {
		return nil, errors.New("witness name is required")
	}
	pub := priv.Public().(ed25519.PublicKey)
	verifiers := make(map[string]*ParsedVerifier)
	for _, vs := range logVerifierStrings {
		if strings.TrimSpace(vs) == "" {
			continue
		}
		pv, err := ParseNoteVerifierString(strings.TrimSpace(vs))
		if err != nil {
			return nil, fmt.Errorf("invalid log verifier %q: %w", vs, err)
		}
		verifiers[pv.Name] = pv
	}
	w := &WitnessEngine{
		Name:         name,
		Operator:     DefaultWitnessOperatorLabel,
		PrivKey:      priv,
		PubKey:       pub,
		StateFile:    stateFile,
		NowUnix:      func() uint64 { return uint64(time.Now().Unix()) },
		LogVerifiers: verifiers,
		state:        make(map[string]OriginState),
	}
	if stateFile != "" {
		if err := w.loadState(); err != nil {
			return nil, err
		}
	}
	return w, nil
}

func (w *WitnessEngine) VerifierString() string {
	return NoteVerifierString(w.Name, NoteKeyCosignature, w.PubKey)
}

func (w *WitnessEngine) loadState() error {
	data, err := os.ReadFile(w.StateFile)
	if err != nil {
		if errors.Is(err, os.ErrNotExist) {
			return nil
		}
		return err
	}
	var persisted map[string]OriginState
	if err := json.Unmarshal(data, &persisted); err != nil {
		return fmt.Errorf("corrupt witness state file: %w", err)
	}
	w.state = persisted
	return nil
}

func (w *WitnessEngine) saveStateLocked() error {
	if w.StateFile == "" {
		return nil
	}
	if err := os.MkdirAll(filepath.Dir(w.StateFile), 0o755); err != nil {
		return err
	}
	data, err := json.MarshalIndent(w.state, "", "  ")
	if err != nil {
		return err
	}
	tmp := w.StateFile + ".tmp"
	if err := os.WriteFile(tmp, data, 0o600); err != nil {
		return err
	}
	return os.Rename(tmp, w.StateFile)
}

func (w *WitnessEngine) verifyLogSignatureIfConfigured(cp *Checkpoint) bool {
	if len(w.LogVerifiers) == 0 {
		return true
	}
	for _, sig := range cp.Signatures {
		v, ok := w.LogVerifiers[sig.Name]
		if !ok || v.KeyType != NoteKeyEd25519 || !bytes.Equal(sig.KeyID, v.KeyID) {
			continue
		}
		if ed25519.Verify(v.PublicKey, []byte(cp.Body), sig.Signature) {
			return true
		}
	}
	return false
}

// ProcessCheckpoint verifies consistency against stored state, updates state atomically, and cosigns.
func (w *WitnessEngine) ProcessCheckpoint(checkpointText string, oldSize int64, proof [][]byte) (string, string, *Checkpoint, error) {
	cp, err := ParseCheckpoint(checkpointText)
	if err != nil {
		return "", "", nil, &WitnessError{StatusCode: http.StatusBadRequest, Code: "bad_checkpoint", Message: err.Error()}
	}
	if !w.verifyLogSignatureIfConfigured(cp) {
		return "", "", nil, &WitnessError{StatusCode: http.StatusForbidden, Code: "invalid_log_signature", Message: "checkpoint does not carry a valid configured log signature"}
	}

	w.mu.Lock()
	defer w.mu.Unlock()

	prev, hasPrev := w.state[cp.Origin]
	if hasPrev {
		prevRoot, err := base64.StdEncoding.DecodeString(prev.RootBase64)
		if err != nil || len(prevRoot) != 32 {
			return "", "", nil, &WitnessError{StatusCode: http.StatusInternalServerError, Code: "corrupt_state", Message: "invalid stored root"}
		}
		if oldSize > 0 && oldSize != prev.TreeSize {
			return "", "", nil, &WitnessError{
				StatusCode: http.StatusConflict,
				Code:       "old_size_mismatch",
				Message:    fmt.Sprintf("request old_size %d does not match witness state %d", oldSize, prev.TreeSize),
			}
		}
		if cp.TreeSize < prev.TreeSize {
			return "", "", nil, &WitnessError{
				StatusCode: http.StatusConflict,
				Code:       "rollback_detected",
				Message:    fmt.Sprintf("checkpoint tree size %d regressed below seen size %d", cp.TreeSize, prev.TreeSize),
			}
		}
		if cp.TreeSize == prev.TreeSize {
			if !bytes.Equal(cp.Root, prevRoot) {
				return "", "", nil, &WitnessError{
					StatusCode: http.StatusConflict,
					Code:       "equivocation_detected",
					Message:    fmt.Sprintf("split-view equivocation at tree size %d: root mismatch", cp.TreeSize),
				}
			}
		} else if prev.TreeSize > 0 {
			if !VerifyConsistency(prev.TreeSize, cp.TreeSize, proof, prevRoot, cp.Root) {
				return "", "", nil, &WitnessError{
					StatusCode: http.StatusUnprocessableEntity,
					Code:       "consistency_failed",
					Message:    fmt.Sprintf("RFC 9162 consistency proof failed from %d to %d", prev.TreeSize, cp.TreeSize),
				}
			}
		}
	} else if oldSize > 0 && oldSize != cp.TreeSize {
		return "", "", nil, &WitnessError{
			StatusCode: http.StatusConflict,
			Code:       "unknown_origin_nonzero_old",
			Message:    fmt.Sprintf("no prior state for origin %s, but old_size=%d was specified", cp.Origin, oldSize),
		}
	}

	now := w.NowUnix()
	sigLine, fullText, err := CosignCheckpoint(checkpointText, w.Name, w.PrivKey, now)
	if err != nil {
		return "", "", nil, &WitnessError{StatusCode: http.StatusBadRequest, Code: "cosign_failed", Message: err.Error()}
	}

	w.state[cp.Origin] = OriginState{
		Origin:     cp.Origin,
		TreeSize:   cp.TreeSize,
		RootBase64: base64.StdEncoding.EncodeToString(cp.Root),
		UpdatedAt:  int64(now),
	}
	if err := w.saveStateLocked(); err != nil {
		return "", "", nil, &WitnessError{StatusCode: http.StatusInternalServerError, Code: "persistence_failed", Message: err.Error()}
	}
	return sigLine, fullText, cp, nil
}

// ParseC2SPAddCheckpointBody parses a C2SP tlog-witness wire request body:
// "old <size>\n<base64-hash-1>\n...\n\n<checkpoint>"
func ParseC2SPAddCheckpointBody(body string) (int64, [][]byte, string, error) {
	sep := strings.Index(body, "\n\n")
	if sep < 0 {
		return 0, nil, "", errors.New("tlog-witness: missing blank line separator")
	}
	headLines := strings.Split(body[:sep], "\n")
	if len(headLines) == 0 {
		return 0, nil, "", errors.New("tlog-witness: empty header")
	}
	first := strings.TrimSpace(headLines[0])
	first = strings.TrimPrefix(first, "old ")
	oldSize, err := strconv.ParseInt(first, 10, 64)
	if err != nil || oldSize < 0 {
		return 0, nil, "", errors.New("tlog-witness: invalid old size")
	}
	var proof [][]byte
	for _, line := range headLines[1:] {
		trimmed := strings.TrimSpace(line)
		if trimmed == "" {
			continue
		}
		h, err := base64.StdEncoding.DecodeString(trimmed)
		if err != nil || len(h) != 32 {
			return 0, nil, "", errors.New("tlog-witness: invalid consistency proof hash")
		}
		proof = append(proof, h)
	}
	return oldSize, proof, body[sep+2:], nil
}

type cosignJSONRequest struct {
	Checkpoint string   `json:"checkpoint"`
	OldSize    int64    `json:"old_size"`
	Proof      []string `json:"proof"`
}

type cosignJSONResponse struct {
	Witness     string `json:"witness"`
	Origin      string `json:"origin"`
	TreeSize    int64  `json:"tree_size"`
	Cosignature string `json:"cosignature"`
	Checkpoint  string `json:"checkpoint"`
	VerifierKey string `json:"verifier_key"`
}

// NewHTTPHandler constructs the HTTP ServeMux for the witness service.
func NewHTTPHandler(engine *WitnessEngine) http.Handler {
	mux := http.NewServeMux()

	mux.HandleFunc("/health", func(rw http.ResponseWriter, req *http.Request) {
		if req.Method != http.MethodGet {
			http.Error(rw, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		engine.mu.Lock()
		originsCount := len(engine.state)
		engine.mu.Unlock()
		rw.Header().Set("Content-Type", "application/json")
		operator := engine.Operator
		if operator == "" {
			operator = DefaultWitnessOperatorLabel
		}
		_ = json.NewEncoder(rw).Encode(map[string]any{
			"status":          "ok",
			"witness":         engine.Name,
			"operator":        operator,
			"verifier_key":    engine.VerifierString(),
			"origins_tracked": originsCount,
		})
	})

	mux.HandleFunc("/verifier-key", func(rw http.ResponseWriter, req *http.Request) {
		if req.Method != http.MethodGet {
			http.Error(rw, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		if req.URL.Query().Get("format") == "text" {
			rw.Header().Set("Content-Type", "text/plain; charset=utf-8")
			_, _ = rw.Write([]byte(engine.VerifierString() + "\n"))
			return
		}
		rw.Header().Set("Content-Type", "application/json")
		operator := engine.Operator
		if operator == "" {
			operator = DefaultWitnessOperatorLabel
		}
		_ = json.NewEncoder(rw).Encode(map[string]any{
			"witness":           engine.Name,
			"operator":          operator,
			"verifier_key":      engine.VerifierString(),
			"public_key_base64": base64.StdEncoding.EncodeToString(engine.PubKey),
		})
	})

	handleCosign := func(rw http.ResponseWriter, req *http.Request, forceText bool) {
		if req.Method != http.MethodPost {
			http.Error(rw, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		rawBody, err := io.ReadAll(io.LimitReader(req.Body, 1<<20))
		if err != nil {
			http.Error(rw, "failed to read body", http.StatusBadRequest)
			return
		}
		contentType := req.Header.Get("Content-Type")
		var oldSize int64
		var proof [][]byte
		var checkpointText string
		isJSON := strings.Contains(contentType, "application/json") || (!forceText && len(rawBody) > 0 && rawBody[0] == '{')

		if isJSON {
			var payload cosignJSONRequest
			if err := json.Unmarshal(rawBody, &payload); err != nil {
				http.Error(rw, "invalid JSON payload", http.StatusBadRequest)
				return
			}
			checkpointText = payload.Checkpoint
			oldSize = payload.OldSize
			for _, p := range payload.Proof {
				h, err := base64.StdEncoding.DecodeString(p)
				if err != nil || len(h) != 32 {
					http.Error(rw, "invalid base64 proof hash", http.StatusBadRequest)
					return
				}
				proof = append(proof, h)
			}
		} else {
			oldSize, proof, checkpointText, err = ParseC2SPAddCheckpointBody(string(rawBody))
			if err != nil {
				http.Error(rw, err.Error(), http.StatusBadRequest)
				return
			}
		}

		sigLine, fullText, cp, err := engine.ProcessCheckpoint(checkpointText, oldSize, proof)
		if err != nil {
			var wErr *WitnessError
			status := http.StatusBadRequest
			code := "witness_error"
			msg := err.Error()
			if errors.As(err, &wErr) {
				status = wErr.StatusCode
				code = wErr.Code
				msg = wErr.Message
			}
			rw.Header().Set("Content-Type", "application/json")
			rw.WriteHeader(status)
			_ = json.NewEncoder(rw).Encode(map[string]any{
				"error":   code,
				"message": msg,
			})
			return
		}

		if forceText || strings.Contains(req.Header.Get("Accept"), "text/plain") || (!isJSON) {
			rw.Header().Set("Content-Type", "text/plain; charset=utf-8")
			_, _ = rw.Write([]byte(sigLine))
			return
		}

		rw.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(rw).Encode(cosignJSONResponse{
			Witness:     engine.Name,
			Origin:      cp.Origin,
			TreeSize:    cp.TreeSize,
			Cosignature: strings.TrimSuffix(sigLine, "\n"),
			Checkpoint:  fullText,
			VerifierKey: engine.VerifierString(),
		})
	}

	mux.HandleFunc("/cosign", func(rw http.ResponseWriter, req *http.Request) {
		handleCosign(rw, req, false)
	})

	mux.HandleFunc("/add-checkpoint", func(rw http.ResponseWriter, req *http.Request) {
		handleCosign(rw, req, true)
	})

	return mux
}

func envOrDefault(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}

// ValidateWitnessCustodyConfig enforces RECEIPTS_MODE=dev|prod key custody rules
// for the witness binary:
//   - In dev mode (default when unset or "dev"): allows WITNESS_SEED_HEX / -seed-hex
//     or ephemeral key generation and returns the "DEV KEYS" boot banner.
//   - In prod mode ("prod"): refuses to start if WITNESS_SEED_HEX / -seed-hex is set
//     or if no FROST share source (WITNESS_FROST_SHARE_SOURCE) is configured.
func ValidateWitnessCustodyConfig(rawMode, seedHex, frostShareSource string) (string, error) {
	mode := rawMode
	if mode == "" {
		mode = "dev"
	}
	if mode != "dev" && mode != "prod" {
		return "", fmt.Errorf("invalid RECEIPTS_MODE %q: must be 'dev' or 'prod'", rawMode)
	}
	if mode == "prod" {
		if seedHex != "" {
			return "", errors.New("[RECEIPTS_MODE=prod] Key custody violation: refusing to use WITNESS_SEED_HEX / -seed-hex in prod mode (FROST threshold signing required)")
		}
		if strings.TrimSpace(frostShareSource) == "" {
			return "", errors.New("[RECEIPTS_MODE=prod] Key custody violation: refusing to generate in-memory witness seed in prod mode (WITNESS_FROST_SHARE_SOURCE required)")
		}
		return "", nil
	}
	return "DEV KEYS: RECEIPTS_MODE=dev (witness seed/file keys permitted for development)", nil
}

func extractHostname(raw string) string {
	s := strings.TrimSpace(strings.ToLower(raw))
	s = strings.TrimPrefix(s, "https://")
	s = strings.TrimPrefix(s, "http://")
	if idx := strings.IndexByte(s, '/'); idx >= 0 {
		s = s[:idx]
	}
	if idx := strings.IndexByte(s, '+'); idx >= 0 {
		s = s[:idx]
	}
	if idx := strings.IndexByte(s, ':'); idx >= 0 {
		s = s[:idx]
	}
	return s
}

// ValidateWitnessColocation enforces in RECEIPTS_MODE=prod that the witness runs
// on infrastructure separate from the Transparency Log, while permitting
// Hypereum-operated witnesses on separate infrastructure when explicitly
// labelled "operated by Hypereum" [OWNER]:
//  1. Refuses if any Transparency Log server env var (RECEIPTS_LOG_KMS_KEY_ID,
//     RECEIPTS_ADMIN_KEY, RECEIPTS_TESSERA_URL, RECEIPTS_S3_BUCKET) is present in
//     the witness process environment.
//  2. Refuses if WITNESS_HOST_ID matches LOG_HOST_ID (when set) or if the
//     witness hostname matches any configured log hostname/origin or loopback.
//  3. Requires a non-empty operator disclosure label (default "operated by Hypereum").
func ValidateWitnessColocation(rawMode, witnessHostOrName, logHostOrOrigin, operatorLabel string, env map[string]string) error {
	mode := strings.TrimSpace(rawMode)
	if mode == "" {
		mode = "dev"
	}
	if mode != "prod" {
		return nil
	}
	if strings.TrimSpace(operatorLabel) == "" {
		return errors.New("[RECEIPTS_MODE=prod] Co-location / operator violation: WITNESS_OPERATOR label is required in prod mode")
	}
	forbiddenLogEnvKeys := []string{
		"RECEIPTS_LOG_KMS_KEY_ID",
		"RECEIPTS_ADMIN_KEY",
		"RECEIPTS_TESSERA_URL",
		"RECEIPTS_S3_BUCKET",
	}
	for _, k := range forbiddenLogEnvKeys {
		if strings.TrimSpace(env[k]) != "" {
			return fmt.Errorf("[RECEIPTS_MODE=prod] Co-location violation: witness environment contains Transparency Log variable %s (witness must run on infrastructure separate from the log)", k)
		}
	}
	wHostID := strings.TrimSpace(env["WITNESS_HOST_ID"])
	lHostID := strings.TrimSpace(env["LOG_HOST_ID"])
	if wHostID != "" && lHostID != "" && strings.EqualFold(wHostID, lHostID) {
		return fmt.Errorf("[RECEIPTS_MODE=prod] Co-location violation: WITNESS_HOST_ID (%s) matches LOG_HOST_ID (%s)", wHostID, lHostID)
	}
	wHost := extractHostname(witnessHostOrName)
	lHost := extractHostname(logHostOrOrigin)
	if wHost == "" || wHost == "localhost" || wHost == "127.0.0.1" || wHost == "::1" {
		return fmt.Errorf("[RECEIPTS_MODE=prod] Co-location violation: witness host %q is loopback or empty", witnessHostOrName)
	}
	if lHost != "" && wHost == lHost {
		return fmt.Errorf("[RECEIPTS_MODE=prod] Co-location violation: witness host %q is co-located with log host %q", wHost, lHost)
	}
	return nil
}

func currentEnvMap() map[string]string {
	m := make(map[string]string)
	for _, kv := range os.Environ() {
		if idx := strings.IndexByte(kv, '='); idx > 0 {
			m[kv[:idx]] = kv[idx+1:]
		}
	}
	return m
}

func main() {
	listenAddr := flag.String("listen", envOrDefault("WITNESS_LISTEN", ":8795"), "HTTP listen address")
	witnessName := flag.String("name", envOrDefault("WITNESS_NAME", "witness.hypereum.dev"), "Witness note signer name")
	operatorLabel := flag.String("operator", envOrDefault("WITNESS_OPERATOR", DefaultWitnessOperatorLabel), "Witness operator disclosure label [OWNER]")
	logHost := flag.String("log-origin", envOrDefault("WITNESS_LOG_ORIGIN", "receipts.hivemindax.com"), "Transparency Log origin/host for co-location check")
	seedHex := flag.String("seed-hex", os.Getenv("WITNESS_SEED_HEX"), "32-byte hex Ed25519 private seed (dev mode only; refused in RECEIPTS_MODE=prod)")
	frostShareSource := flag.String("frost-share-source", envOrDefault("WITNESS_FROST_SHARE_SOURCE", ""), "FROST threshold share source URI for RECEIPTS_MODE=prod")
	stateFile := flag.String("state-file", envOrDefault("WITNESS_STATE_FILE", ""), "Path to persistent JSON state file")
	logVerifiersCSV := flag.String("log-verifiers", os.Getenv("WITNESS_LOG_VERIFIERS"), "Comma-separated list of trusted log note verifier strings")
	flag.Parse()

	banner, err := ValidateWitnessCustodyConfig(os.Getenv("RECEIPTS_MODE"), *seedHex, *frostShareSource)
	if err != nil {
		log.Fatalf("%v", err)
	}
	if err := ValidateWitnessColocation(os.Getenv("RECEIPTS_MODE"), *witnessName, *logHost, *operatorLabel, currentEnvMap()); err != nil {
		log.Fatalf("%v", err)
	}
	if banner != "" {
		log.Println(banner)
	}

	var priv ed25519.PrivateKey
	if *seedHex != "" {
		seed, err := hex.DecodeString(*seedHex)
		if err != nil || len(seed) != ed25519.SeedSize {
			log.Fatalf("WITNESS_SEED_HEX must be a 64-char hex string (32 bytes)")
		}
		priv = ed25519.NewKeyFromSeed(seed)
	} else {
		_, generatedPriv, err := ed25519.GenerateKey(rand.Reader)
		if err != nil {
			log.Fatalf("failed to generate Ed25519 key: %v", err)
		}
		priv = generatedPriv
	}

	var verifiers []string
	if *logVerifiersCSV != "" {
		verifiers = strings.Split(*logVerifiersCSV, ",")
	}

	engine, err := NewWitnessEngine(*witnessName, priv, *stateFile, verifiers)
	if err != nil {
		log.Fatalf("failed to initialize witness engine: %v", err)
	}
	engine.Operator = *operatorLabel

	log.Printf("receipts-witness %q listening on %s (verifier: %s)", engine.Name, *listenAddr, engine.VerifierString())
	srv := &http.Server{
		Addr:              *listenAddr,
		Handler:           NewHTTPHandler(engine),
		ReadHeaderTimeout: 5 * time.Second,
	}
	if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
		log.Fatalf("witness server failed: %v", err)
	}
}
