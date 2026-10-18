---
upstream: not-filing
checked: 2026-10-18
links:
---

# raft: reads postponed until a new leader's first commit are not released when a configuration change commits it

- **Status**: not a bug for an application that follows `doc.go` (analysis 2026-10-18, by code reading); reachable
  only through the misuse recorded in [raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md)
  (`Advance` before `ApplyConfChange`), so not filed on its own. Raised by a code review of the
  `raft-readindex-singleton-stale` fix, which does not change this code.
- **Where** (etcd-io/raft `main` 638f42739): `stepLeader`, `MsgReadIndex` (`raft.go:1363-1368`) postpones a read
  until the leader has committed an entry in its term; `releasePendingReadIndexMessages` is called only from the
  `MsgAppResp` case after `maybeCommit` (`raft.go:1542-1545`). `switchToConfig` also calls `maybeCommit`
  (`raft.go:2006`) and then only `bcastAppend`s, without releasing the postponed reads.
- **What would happen**: a leader with postponed reads applies a conf change whose new quorum lets
  `switchToConfig`'s `maybeCommit` commit the leader's first entry of its term; the reads would stay queued until a
  later commit goes through `MsgAppResp`.
- **Why it does not, under `doc.go`'s protocol**: the conf change applied at the leader was committed either
  - before the leader's term: then it was applied before the election, since `hup` refuses to campaign while
    committed conf changes are unapplied (`raft.go:983-986`, against `raftLog.applied`, which `Advance` moves); or
  - in the leader's term: then the leader had already committed in its term, through the `MsgAppResp` path (a
    leader's commit index advances only by counting acknowledgements), which released the reads.

  An application that calls `Advance` before `ApplyConfChange` breaks the first case: the campaign check passes
  while a committed conf change is still to be applied. Tests that call `becomeLeader` directly skip the check too.
- **How the proof handles it**: liveness; the proofs state safety only.
- **Possible fixes** (if wanted as hardening): release the postponed reads after `switchToConfig`'s `maybeCommit`
  when `committedEntryInCurrentTerm()` holds, as `MsgAppResp` does.
- **Found**: 2026-10-18, the code review of the upstream fix branch `fix/raft-readindex-singleton-stale`.
