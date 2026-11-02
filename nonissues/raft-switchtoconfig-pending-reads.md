---
upstream: none
checked: 2026-11-01
links:
blocks-proof: no
---
# raft: reads postponed until a new leader's first commit are not released when a configuration change makes that commit

A leader postpones `MsgReadIndex` until it has committed an entry in its term, and releases the
postponed reads only from the `MsgAppResp` path after `maybeCommit`. `switchToConfig` also calls
`maybeCommit` (a new quorum can commit the leader's first entry of its term) but does not release
them, so they would wait for a later commit.

**Why not an issue:** no test, found by code reading, and unreachable under doc.go's protocol: a
conf change applied at a leader was either committed before its term (then applied before the
election, as `hup` refuses to campaign with unapplied conf changes) or in its term (then the
leader had already committed in its term through `MsgAppResp`, which released the reads). Only the
`Advance`-before-`ApplyConfChange` order of
[`raft-advance-before-applyconfchange`](../issues/raft-advance-before-applyconfchange.md) reaches it.

## Proof

no: liveness; the proofs state safety only.

## Notes

Hardening, if wanted: release the postponed reads after `switchToConfig`'s `maybeCommit` when
`committedEntryInCurrentTerm()` holds. Found 2026-10-18, the code review of the
`raft-readindex-singleton-stale` fix branch. Upstream searched 2026-11-01 (`pendingReadIndexMessages switchToConfig`, `releasePendingReadIndexMessages`): nothing.
