> **Retired preview, not maintained.**

# `receipts-witness` — Standalone C2SP `tlog-witness` & RFC 9162 Consistency Verifier

SPDX-License-Identifier: Apache-2.0

`receipts-witness` is a standalone, zero-dependency Go binary that operates an independent C2SP [`tlog-witness`](https://c2sp.org/tlog-witness) and [`tlog-cosignature`](https://c2sp.org/tlog-cosignature) cosigner for SCITT and RFC 9162 transparency logs.

## Features

- **RFC 9162 §2.1.4.2 Consistency Proof Verification (`VerifyConsistency`)**: Cryptographically verifies append-only tree transitions (`firstSize -> secondSize`) over SHA-256 Merkle trees (`0x00` leaf prefix, `0x01` interior node prefix).
- **C2SP `tlog-cosignature/v1` (`CosignCheckpoint`)**: Produces standard Ed25519 witness cosignatures (key type `0x04`, 8-byte big-endian Unix timestamp + 64-byte Ed25519 signature over `cosignature/v1\ntime <ts>\n<checkpoint-body>`).
- **Split-View & Anti-Rollback Protection**: Rejects tree size regressions (`409 Conflict`) and same-size root equivocations (`409 Conflict`), persisting state atomically to disk.
- **HTTP Endpoints**:
  - `POST /cosign` — JSON (`{ checkpoint, old_size, proof }`) or C2SP wire format.
  - `POST /add-checkpoint` — Standard C2SP `tlog-witness` wire endpoint (`old <size>\n<base64-hashes>\n\n<checkpoint>`).
  - `GET /health` — Health status and tracked origin count.
  - `GET /verifier-key` — Returns the C2SP note verifier string (`<name>+<keyid>+<base64>`).

## Usage

```bash
go test ./...
go run . --listen :8795 --name witness-1.example.org --state-file /var/lib/receipts-witness/state.json
```
