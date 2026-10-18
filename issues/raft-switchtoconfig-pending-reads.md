---
upstream: unchecked
checked: 2026-10-18
links:
---

# raft: reads postponed until a new leader's first commit are not released when a configuration change commits it

- **Status**: possible bug (liveness: read index requests wait longer than needed, not a wrong result); from a
  code review of the `raft-readindex-singleton-stale` fix (2026-10-18), by code reading only, not reproduced.
- **Where** (etcd-io/raft `main` 638f42739): `stepLeader`, `MsgReadIndex` (`raft.go:1363-1368`) appends a read to
  `pendingReadIndexMessages` until the leader has committed an entry in its term; `releasePendingReadIndexMessages`
  is called only from `stepLeader`'s `MsgAppResp` case after `maybeCommit`. `switchToConfig` (`raft.go`, the end of
  the function) also calls `maybeCommit` when the new configuration changes the quorum, and then only
  `bcastAppend`s; it does not release the postponed reads.
- **What happens**: a leader of `{L, F}` is elected and appends its empty entry, but `F` is unreachable, so the
  entry does not commit and reads are postponed. `L` then applies an already committed removal of `F`: in `{L}`,
  `switchToConfig`'s `maybeCommit` commits the empty entry, so `committedEntryInCurrentTerm()` becomes true, but the
  postponed reads stay queued until a later commit goes through `MsgAppResp` (the next proposal). Reads arriving
  after the switch are answered at once; only those already queued wait.
- **Expected**: postponed reads are released as soon as the leader has committed an entry in its term, whatever
  path committed it.
- **How the proof handles it**: liveness; the proofs state safety only.
- **Possible fixes**: call `releasePendingReadIndexMessages(r)` after `switchToConfig`'s `maybeCommit` when
  `committedEntryInCurrentTerm()` holds (as `MsgAppResp` does).
- **Found**: 2026-10-18, the code review of the upstream fix branch `fix/raft-readindex-singleton-stale`.
