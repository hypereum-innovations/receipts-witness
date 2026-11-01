// SPDX-License-Identifier: Apache-2.0
/**
 * Split-View Gossip Protocol & Equivocation Proof Auditor (`GossipAuditor`).
 *
 * Accepts signed C2SP checkpoints observed from multiple peers/sources for the
 * same log `origin`. Detects split-view attacks when:
 *  1. Two checkpoints for the same `origin` have the same `treeSize` and
 *     different `rootHash` (`reason: 'conflicting_roots_same_size'`), or
 *  2. Two checkpoints have `size1 < size2` and the RFC 9162 Merkle consistency
 *     proof between them fails (`reason: 'consistency_proof_failed'`).
 *
 * Produces a self-contained, offline-verifiable `EquivocationProof` that any
 * third party can verify via `verifyEquivocationProof`.
 */
import {
  parseCheckpoint,
  verifyCheckpointSignatures,
  type Checkpoint,
} from '../core/checkpoint.js';
import { verifyConsistency, type ConsistencyProof } from '../core/merkle.js';

export interface ObservedCheckpointSummary {
  text: string;
  origin: string;
  treeSize: number;
  rootHash: string;
  source: string;
  observedAt: string;
}

export interface SerializedConsistencyProof {
  firstSize: number;
  secondSize: number;
  hashes: string[]; // base64
}

export interface EquivocationProof {
  origin: string;
  checkpointA: ObservedCheckpointSummary;
  checkpointB: ObservedCheckpointSummary;
  reason: 'conflicting_roots_same_size' | 'consistency_proof_failed';
  consistencyProof?: SerializedConsistencyProof;
  detectedAt: string;
}

export interface GossipSubmissionInput {
  checkpointText: string;
  source?: string;
  consistencyProof?:
    | ConsistencyProof
    | { firstSize: number; secondSize: number; hashes: Array<Buffer | string> }
    | null;
}

export interface GossipSubmissionResult {
  status: 'consistent' | 'equivocation_detected';
  origin: string;
  treeSize: number;
  rootHash: string;
  equivocationProof: EquivocationProof | null;
}

function normalizeConsistencyProof(
  p: NonNullable<GossipSubmissionInput['consistencyProof']>,
): ConsistencyProof {
  return {
    firstSize: Number(p.firstSize),
    secondSize: Number(p.secondSize),
    hashes: p.hashes.map((h) => (Buffer.isBuffer(h) ? h : Buffer.from(String(h), 'base64'))),
  };
}

function serializeConsistencyProof(p: ConsistencyProof): SerializedConsistencyProof {
  return {
    firstSize: p.firstSize,
    secondSize: p.secondSize,
    hashes: p.hashes.map((h) => h.toString('base64')),
  };
}

interface StoredObservation {
  summary: ObservedCheckpointSummary;
  checkpoint: Checkpoint;
}

export class GossipAuditor {
  private readonly observationsByOrigin = new Map<string, StoredObservation[]>();
  private readonly equivocations: EquivocationProof[] = [];

  constructor(
    private readonly opts: {
      /** Optional C2SP note verifier strings for log signature verification on ingest. */
      logVerifiers?: string[];
      /** Optional callback to fetch consistency proofs between two sizes for an origin. */
      consistencyProvider?: (
        origin: string,
        firstSize: number,
        secondSize: number,
      ) => ConsistencyProof | null;
    } = {},
  ) {}

  getEquivocations(origin?: string): EquivocationProof[] {
    if (!origin) return [...this.equivocations];
    return this.equivocations.filter((e) => e.origin === origin);
  }

  getObservations(origin: string): ObservedCheckpointSummary[] {
    return (this.observationsByOrigin.get(origin) ?? []).map((o) => o.summary);
  }

  /**
   * Submit an observed checkpoint from a peer/source and check it against all
   * previously seen checkpoints for the same `origin`.
   */
  submitCheckpoint(input: GossipSubmissionInput): GossipSubmissionResult {
    const { checkpoint } = parseCheckpoint(input.checkpointText);
    if (this.opts.logVerifiers && this.opts.logVerifiers.length > 0) {
      const sig = verifyCheckpointSignatures(input.checkpointText, this.opts.logVerifiers);
      if (!sig.logValid) {
        throw new Error(`gossip: checkpoint for ${checkpoint.origin} does not carry a valid log signature`);
      }
    }

    const rootHash = `sha256:${checkpoint.root.toString('hex')}`;
    const now = new Date().toISOString();
    const summary: ObservedCheckpointSummary = {
      text: input.checkpointText,
      origin: checkpoint.origin,
      treeSize: checkpoint.treeSize,
      rootHash,
      source: input.source ?? 'peer',
      observedAt: now,
    };

    const history = this.observationsByOrigin.get(checkpoint.origin) ?? [];
    const suppliedProof = input.consistencyProof
      ? normalizeConsistencyProof(input.consistencyProof)
      : null;

    for (const prev of history) {
      // Case 1: Same treeSize, different rootHash -> immediate split-view equivocation
      if (prev.checkpoint.treeSize === checkpoint.treeSize) {
        if (!prev.checkpoint.root.equals(checkpoint.root)) {
          const proof: EquivocationProof = {
            origin: checkpoint.origin,
            checkpointA: prev.summary,
            checkpointB: summary,
            reason: 'conflicting_roots_same_size',
            detectedAt: now,
          };
          this.equivocations.push(proof);
          history.push({ summary, checkpoint });
          this.observationsByOrigin.set(checkpoint.origin, history);
          return {
            status: 'equivocation_detected',
            origin: checkpoint.origin,
            treeSize: checkpoint.treeSize,
            rootHash,
            equivocationProof: proof,
          };
        }
        continue;
      }

      // Case 2: Different treeSize -> verify Merkle consistency if a proof is supplied or available
      const smaller =
        prev.checkpoint.treeSize < checkpoint.treeSize ? prev : { summary, checkpoint };
      const larger =
        prev.checkpoint.treeSize < checkpoint.treeSize ? { summary, checkpoint } : prev;

      let candidateProof: ConsistencyProof | null = null;
      if (
        suppliedProof &&
        suppliedProof.firstSize === smaller.checkpoint.treeSize &&
        suppliedProof.secondSize === larger.checkpoint.treeSize
      ) {
        candidateProof = suppliedProof;
      } else if (this.opts.consistencyProvider) {
        try {
          candidateProof = this.opts.consistencyProvider(
            checkpoint.origin,
            smaller.checkpoint.treeSize,
            larger.checkpoint.treeSize,
          );
        } catch {
          candidateProof = null;
        }
      } else if (suppliedProof) {
        candidateProof = suppliedProof;
      }

      if (candidateProof && smaller.checkpoint.treeSize > 0) {
        const consistent = verifyConsistency(
          candidateProof,
          smaller.checkpoint.root,
          larger.checkpoint.root,
        );
        if (!consistent) {
          const proof: EquivocationProof = {
            origin: checkpoint.origin,
            checkpointA: smaller.summary,
            checkpointB: larger.summary,
            reason: 'consistency_proof_failed',
            consistencyProof: serializeConsistencyProof(candidateProof),
            detectedAt: now,
          };
          this.equivocations.push(proof);
          history.push({ summary, checkpoint });
          this.observationsByOrigin.set(checkpoint.origin, history);
          return {
            status: 'equivocation_detected',
            origin: checkpoint.origin,
            treeSize: checkpoint.treeSize,
            rootHash,
            equivocationProof: proof,
          };
        }
      }
    }

    history.push({ summary, checkpoint });
    this.observationsByOrigin.set(checkpoint.origin, history);
    return {
      status: 'consistent',
      origin: checkpoint.origin,
      treeSize: checkpoint.treeSize,
      rootHash,
      equivocationProof: null,
    };
  }

  /** Alias for `submitCheckpoint`. */
  observeCheckpoint(input: GossipSubmissionInput): GossipSubmissionResult {
    return this.submitCheckpoint(input);
  }
}

/**
 * Offline verification of an `EquivocationProof`.
 * Checks that both checkpoints parse for the same `origin`, verifies log
 * signatures if `verifiers` are provided, and confirms either:
 *  - `conflicting_roots_same_size`: `treeSizeA === treeSizeB` and `rootA !== rootB`, or
 *  - `consistency_proof_failed`: `treeSizeA < treeSizeB` and `verifyConsistency` fails.
 */
export function verifyEquivocationProof(
  proof: {
    origin: string;
    checkpointA: ObservedCheckpointSummary | string;
    checkpointB: ObservedCheckpointSummary | string;
    reason: 'conflicting_roots_same_size' | 'consistency_proof_failed';
    consistencyProof?: SerializedConsistencyProof | ConsistencyProof;
    detectedAt: string;
  },
  verifiers?: string[],
): { valid: boolean; detail: string } {
  try {
    const textA = typeof proof.checkpointA === 'string' ? proof.checkpointA : proof.checkpointA.text;
    const textB = typeof proof.checkpointB === 'string' ? proof.checkpointB : proof.checkpointB.text;

    const parsedA = parseCheckpoint(textA);
    const parsedB = parseCheckpoint(textB);

    if (parsedA.checkpoint.origin !== proof.origin || parsedB.checkpoint.origin !== proof.origin) {
      return { valid: false, detail: 'checkpoint origins do not match proof.origin' };
    }

    if (verifiers && verifiers.length > 0) {
      const sigA = verifyCheckpointSignatures(textA, verifiers);
      const sigB = verifyCheckpointSignatures(textB, verifiers);
      if (!sigA.logValid || !sigB.logValid) {
        return { valid: false, detail: 'one or both checkpoints lack a valid log signature' };
      }
    }

    if (proof.reason === 'conflicting_roots_same_size') {
      if (parsedA.checkpoint.treeSize !== parsedB.checkpoint.treeSize) {
        return {
          valid: false,
          detail: `expected equal tree sizes for conflicting_roots_same_size, got ${parsedA.checkpoint.treeSize} and ${parsedB.checkpoint.treeSize}`,
        };
      }
      if (parsedA.checkpoint.root.equals(parsedB.checkpoint.root)) {
        return { valid: false, detail: 'roots are identical; no equivocation' };
      }
      return {
        valid: true,
        detail: `equivocation verified: origin ${proof.origin} signed two distinct roots at size ${parsedA.checkpoint.treeSize}`,
      };
    }

    if (proof.reason === 'consistency_proof_failed') {
      if (parsedA.checkpoint.treeSize === parsedB.checkpoint.treeSize) {
        return { valid: false, detail: 'tree sizes are equal; expected size1 < size2 for consistency_proof_failed' };
      }
      const smaller =
        parsedA.checkpoint.treeSize < parsedB.checkpoint.treeSize
          ? parsedA.checkpoint
          : parsedB.checkpoint;
      const larger =
        parsedA.checkpoint.treeSize < parsedB.checkpoint.treeSize
          ? parsedB.checkpoint
          : parsedA.checkpoint;

      if (!proof.consistencyProof) {
        return { valid: false, detail: 'missing consistencyProof for consistency_proof_failed' };
      }
      const normProof = normalizeConsistencyProof(proof.consistencyProof);
      const consistent = verifyConsistency(normProof, smaller.root, larger.root);
      if (consistent) {
        return { valid: false, detail: 'consistency proof actually verifies; no equivocation' };
      }
      return {
        valid: true,
        detail: `equivocation verified: consistency proof from size ${smaller.treeSize} to ${larger.treeSize} failed for ${proof.origin}`,
      };
    }

    return { valid: false, detail: `unknown equivocation reason ${String(proof.reason)}` };
  } catch (e) {
    return { valid: false, detail: (e as Error).message };
  }
}
