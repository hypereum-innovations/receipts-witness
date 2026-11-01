// SPDX-License-Identifier: Apache-2.0
package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"testing"
)

func deterministicKey(label string) ed25519.PrivateKey {
	seed := sha256.Sum256([]byte(label))
	return ed25519.NewKeyFromSeed(seed[:])
}

func makeLeaves(n int) [][]byte {
	leaves := make([][]byte, n)
	for i := 0; i < n; i++ {
		leaves[i] = LeafHash([]byte(fmt.Sprintf("capsule-leaf-%d", i)))
	}
	return leaves
}

func TestVerifyConsistencyExhaustiveSizes(t *testing.T) {
	leaves := makeLeaves(35)
	for secondSize := 1; secondSize <= 35; secondSize++ {
		secondRoot := MerkleTreeHash(leaves[:secondSize])
		for firstSize := 1; firstSize <= secondSize; firstSize++ {
			firstRoot := MerkleTreeHash(leaves[:firstSize])
			proof, err := BuildConsistencyProof( int64(firstSize), leaves[:secondSize])
			if err != nil {
				t.Fatalf("BuildConsistencyProof(%d, %d) failed: %v", firstSize, secondSize, err)
			}
			if !VerifyConsistency(int64(firstSize), int64(secondSize), proof, firstRoot, secondRoot) {
				t.Fatalf("VerifyConsistency failed for valid proof (%d -> %d)", firstSize, secondSize)
			}

			// Tamper with secondRoot -> must fail
			badRoot := append([]byte{}, secondRoot...)
			badRoot[0] ^= 0xff
			if VerifyConsistency(int64(firstSize), int64(secondSize), proof, firstRoot, badRoot) {
				t.Fatalf("VerifyConsistency accepted tampered secondRoot (%d -> %d)", firstSize, secondSize)
			}

			// Tamper with a proof node -> must fail
			if len(proof) > 0 {
				tamperedProof := make([][]byte, len(proof))
				for i := range proof {
					tamperedProof[i] = append([]byte{}, proof[i]...)
				}
				tamperedProof[0][0] ^= 0x80
				if VerifyConsistency(int64(firstSize), int64(secondSize), tamperedProof, firstRoot, secondRoot) {
					t.Fatalf("VerifyConsistency accepted tampered proof (%d -> %d)", firstSize, secondSize)
				}
			}
		}
	}
}

func TestCosignCheckpointAndVerify(t *testing.T) {
	logPriv := deterministicKey("log-key-1")
	witnessPriv := deterministicKey("witness-key-1")
	origin := "receipts.hypereum.dev/log/2026"
	leaves := makeLeaves(8)
	root := MerkleTreeHash(leaves)

	cpText, err := FormatCheckpoint(origin, 8, root, origin, logPriv)
	if err != nil {
		t.Fatalf("FormatCheckpoint failed: %v", err)
	}

	sigLine, fullCp, err := CosignCheckpoint(cpText, "witness-eu-1.hypereum.dev", witnessPriv, 1761868800)
	if err != nil {
		t.Fatalf("CosignCheckpoint failed: %v", err)
	}
	if !strings.HasPrefix(sigLine, "— witness-eu-1.hypereum.dev ") {
		t.Fatalf("unexpected signature line format: %q", sigLine)
	}

	verifier := NoteVerifierString("witness-eu-1.hypereum.dev", NoteKeyCosignature, witnessPriv.Public().(ed25519.PublicKey))
	ts, valid, err := VerifyCosignature(fullCp, verifier)
	if err != nil || !valid {
		t.Fatalf("VerifyCosignature failed: valid=%v err=%v", valid, err)
	}
	if ts != 1761868800 {
		t.Fatalf("expected timestamp 1761868800, got %d", ts)
	}
}

func TestAntiRollbackEquivocationAndPersistence(t *testing.T) {
	tmpDir := t.TempDir()
	stateFile := filepath.Join(tmpDir, "witness-state.json")

	logPriv := deterministicKey("log-origin-key")
	witnessPriv := deterministicKey("witness-origin-key")
	origin := "receipts.hypereum.dev/v1"
	logVerifier := NoteVerifierString(origin, NoteKeyEd25519, logPriv.Public().(ed25519.PublicKey))

	engine, err := NewWitnessEngine("witness-1", witnessPriv, stateFile, []string{logVerifier})
	if err != nil {
		t.Fatalf("NewWitnessEngine failed: %v", err)
	}
	engine.NowUnix = func() uint64 { return 1761870000 }

	leaves := makeLeaves(10)
	root4 := MerkleTreeHash(leaves[:4])
	cp4, err := FormatCheckpoint(origin, 4, root4, origin, logPriv)
	if err != nil {
		t.Fatalf("FormatCheckpoint(4) failed: %v", err)
	}

	// 1. First checkpoint at size 4 (oldSize=0) succeeds
	_, cosigned4, _, err := engine.ProcessCheckpoint(cp4, 0, nil)
	if err != nil {
		t.Fatalf("initial ProcessCheckpoint(4) failed: %v", err)
	}
	if _, ok, _ := VerifyCosignature(cosigned4, engine.VerifierString()); !ok {
		t.Fatalf("cosignature on size 4 did not verify")
	}

	// 2. Equivocation at size 4 (different root) must fail with equivocation_detected
	fakeRoot4 := sha256.Sum256([]byte("forked-tree-root"))
	cp4Fork, _ := FormatCheckpoint(origin, 4, fakeRoot4[:], origin, logPriv)
	if _, _, _, err := engine.ProcessCheckpoint(cp4Fork, 4, nil); err == nil {
		t.Fatalf("expected equivocation at size 4 to be rejected")
	}

	// 3. Rollback to size 3 must fail with rollback_detected
	root3 := MerkleTreeHash(leaves[:3])
	cp3, _ := FormatCheckpoint(origin, 3, root3, origin, logPriv)
	if _, _, _, err := engine.ProcessCheckpoint(cp3, 4, nil); err == nil {
		t.Fatalf("expected rollback from 4 to 3 to be rejected")
	}

	// 4. Advance from size 4 to size 10 with valid RFC 9162 consistency proof -> succeeds
	root10 := MerkleTreeHash(leaves[:10])
	cp10, _ := FormatCheckpoint(origin, 10, root10, origin, logPriv)
	proof4To10, err := BuildConsistencyProof(4, leaves[:10])
	if err != nil {
		t.Fatalf("BuildConsistencyProof(4->10) failed: %v", err)
	}
	_, cosigned10, _, err := engine.ProcessCheckpoint(cp10, 4, proof4To10)
	if err != nil {
		t.Fatalf("ProcessCheckpoint(4->10) failed: %v", err)
	}
	if _, ok, _ := VerifyCosignature(cosigned10, engine.VerifierString()); !ok {
		t.Fatalf("cosignature on size 10 did not verify")
	}

	// 5. Reload engine from disk stateFile and ensure rollback to size 7 is rejected
	reloaded, err := NewWitnessEngine("witness-1", witnessPriv, stateFile, []string{logVerifier})
	if err != nil {
		t.Fatalf("reload NewWitnessEngine failed: %v", err)
	}
	root7 := MerkleTreeHash(leaves[:7])
	cp7, _ := FormatCheckpoint(origin, 7, root7, origin, logPriv)
	if _, _, _, err := reloaded.ProcessCheckpoint(cp7, 7, nil); err == nil {
		t.Fatalf("expected reloaded engine to reject rollback to size 7")
	}
}

func TestHTTPEndpoints(t *testing.T) {
	logPriv := deterministicKey("http-log-key")
	witnessPriv := deterministicKey("http-witness-key")
	origin := "receipts.hypereum.dev/http"
	logVerifier := NoteVerifierString(origin, NoteKeyEd25519, logPriv.Public().(ed25519.PublicKey))

	engine, err := NewWitnessEngine("witness-http", witnessPriv, "", []string{logVerifier})
	if err != nil {
		t.Fatalf("NewWitnessEngine: %v", err)
	}
	srv := httptest.NewServer(NewHTTPHandler(engine))
	defer srv.Close()

	// 1. GET /health
	resHealth, err := http.Get(srv.URL + "/health")
	if err != nil || resHealth.StatusCode != http.StatusOK {
		t.Fatalf("GET /health failed: %v", err)
	}
	resHealth.Body.Close()

	// 2. GET /verifier-key
	resKey, err := http.Get(srv.URL + "/verifier-key")
	if err != nil || resKey.StatusCode != http.StatusOK {
		t.Fatalf("GET /verifier-key failed: %v", err)
	}
	var keyBody map[string]any
	_ = json.NewDecoder(resKey.Body).Decode(&keyBody)
	resKey.Body.Close()
	if keyBody["verifier_key"] != engine.VerifierString() {
		t.Fatalf("verifier_key mismatch: got %v", keyBody["verifier_key"])
	}

	// 3. POST /cosign (JSON)
	leaves := makeLeaves(6)
	root3 := MerkleTreeHash(leaves[:3])
	cp3, _ := FormatCheckpoint(origin, 3, root3, origin, logPriv)
	reqBody1, _ := json.Marshal(map[string]any{
		"checkpoint": cp3,
		"old_size":   0,
		"proof":      []string{},
	})
	resCosign1, err := http.Post(srv.URL+"/cosign", "application/json", bytes.NewReader(reqBody1))
	if err != nil || resCosign1.StatusCode != http.StatusOK {
		t.Fatalf("POST /cosign (size 3) failed: status=%d err=%v", resCosign1.StatusCode, err)
	}
	var cosignResp1 cosignJSONResponse
	_ = json.NewDecoder(resCosign1.Body).Decode(&cosignResp1)
	resCosign1.Body.Close()
	if cosignResp1.TreeSize != 3 || !strings.HasPrefix(cosignResp1.Cosignature, "— witness-http ") {
		t.Fatalf("unexpected cosign response: %+v", cosignResp1)
	}

	// 4. POST /cosign advancing from 3 to 6 with RFC 9162 proof
	root6 := MerkleTreeHash(leaves[:6])
	cp6, _ := FormatCheckpoint(origin, 6, root6, origin, logPriv)
	proof3To6, _ := BuildConsistencyProof(3, leaves[:6])
	proofB64 := make([]string, len(proof3To6))
	for i, h := range proof3To6 {
		proofB64[i] = base64.StdEncoding.EncodeToString(h)
	}
	reqBody2, _ := json.Marshal(map[string]any{
		"checkpoint": cp6,
		"old_size":   3,
		"proof":      proofB64,
	})
	resCosign2, err := http.Post(srv.URL+"/cosign", "application/json", bytes.NewReader(reqBody2))
	if err != nil || resCosign2.StatusCode != http.StatusOK {
		t.Fatalf("POST /cosign (3->6) failed: status=%d err=%v", resCosign2.StatusCode, err)
	}
	resCosign2.Body.Close()
}

func TestWitnessCustodyProdRefusal(t *testing.T) {
	// 1. Dev mode prints "DEV KEYS" and allows seedHex or generated seed
	banner, err := ValidateWitnessCustodyConfig("dev", "01020304", "")
	if err != nil {
		t.Fatalf("expected dev mode to succeed, got: %v", err)
	}
	if !strings.Contains(banner, "DEV KEYS") {
		t.Fatalf("expected DEV KEYS banner in dev mode, got %q", banner)
	}

	// 2. Prod mode refuses WITNESS_SEED_HEX / -seed-hex
	if _, err := ValidateWitnessCustodyConfig("prod", "deadbeef", "kms://frost-share-1"); err == nil || !strings.Contains(err.Error(), "[RECEIPTS_MODE=prod] Key custody violation") {
		t.Fatalf("expected prod mode to refuse WITNESS_SEED_HEX, got: %v", err)
	}

	// 3. Prod mode refuses empty frostShareSource (ephemeral local seed fallback)
	if _, err := ValidateWitnessCustodyConfig("prod", "", ""); err == nil || !strings.Contains(err.Error(), "[RECEIPTS_MODE=prod] Key custody violation") {
		t.Fatalf("expected prod mode to refuse empty frostShareSource, got: %v", err)
	}

	// 4. Prod mode succeeds when frostShareSource is provided and seedHex is empty
	if _, err := ValidateWitnessCustodyConfig("prod", "", "kms://frost-share-1"); err != nil {
		t.Fatalf("expected prod mode with frostShareSource to succeed, got: %v", err)
	}
}

func TestWitnessColocationAndLaunchDefault(t *testing.T) {
	// 1. Launch default [OWNER]: Hypereum-operated witness on separate infrastructure,
	//    labelled "operated by Hypereum" (DefaultWitnessOperatorLabel) -> PASSES.
	sepEnv := map[string]string{
		"WITNESS_HOST_ID": "witness-eu-west-1a",
		"LOG_HOST_ID":     "log-eu-central-1a",
	}
	if err := ValidateWitnessColocation("prod", "witness-eu-1.hivemindax.com", "receipts.hivemindax.com/2026", DefaultWitnessOperatorLabel, sepEnv); err != nil {
		t.Fatalf("expected launch default (Hypereum-operated witness on separate infrastructure labelled %q) to pass co-location check, got: %v", DefaultWitnessOperatorLabel, err)
	}

	// 2. Co-located hostname (witness host == log host) -> FAILS in prod mode.
	if err := ValidateWitnessColocation("prod", "receipts.hivemindax.com", "receipts.hivemindax.com/2026", DefaultWitnessOperatorLabel, nil); err == nil || !strings.Contains(err.Error(), "co-located with log host") {
		t.Fatalf("expected co-located hostname to fail, got: %v", err)
	}

	// 3. Co-located host ID (WITNESS_HOST_ID == LOG_HOST_ID) -> FAILS in prod mode.
	sameHostEnv := map[string]string{
		"WITNESS_HOST_ID": "node-eu-1",
		"LOG_HOST_ID":     "node-eu-1",
	}
	if err := ValidateWitnessColocation("prod", "witness-eu-1.hivemindax.com", "receipts.hivemindax.com/2026", DefaultWitnessOperatorLabel, sameHostEnv); err == nil || !strings.Contains(err.Error(), "WITNESS_HOST_ID") {
		t.Fatalf("expected matching WITNESS_HOST_ID and LOG_HOST_ID to fail, got: %v", err)
	}

	// 4. Shared process environment containing Transparency Log variables -> FAILS in prod mode.
	sharedLogEnv := map[string]string{
		"RECEIPTS_LOG_KMS_KEY_ID": "arn:aws:kms:eu-central-1:038848608588:key/log-key",
	}
	if err := ValidateWitnessColocation("prod", "witness-eu-1.hivemindax.com", "receipts.hivemindax.com/2026", DefaultWitnessOperatorLabel, sharedLogEnv); err == nil || !strings.Contains(err.Error(), "RECEIPTS_LOG_KMS_KEY_ID") {
		t.Fatalf("expected witness environment with RECEIPTS_LOG_KMS_KEY_ID to fail, got: %v", err)
	}
}
