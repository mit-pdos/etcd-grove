# raft: entries persisted without their `HardState.Commit` can break membership safety

- **Status**: open (documentation precondition; plausibility only, not demonstrated on etcd).
- **Where**: etcd-raft at the pinned revision: `hasUnappliedConfChanges` (`raft.go:990`)
  scans `(applied, committed]` with the *persisted* commit after a restart; `doc.go:74-76`
  (step 1 of handling a `Ready`) asks to write the entries, the `HardState` and the snapshot
  but does not require them to be persisted atomically.
- **What happens**: plain Raft treats the commit index as volatile; etcd-raft's election
  guard against unapplied conf changes makes it safety-relevant. Execution: leader 3 commits
  and applies `C1 = add 4`, proposes `C2 = remove 2`; node 1 receives indices 1–3 with
  `Commit = 2`, persists the entries but crashes before the new `HardState.Commit` is durable,
  and restarts with commit 0 and configuration `C0 = {1,2,3}`; `C2` commits and node 3
  applies it (`{1,3,4}`); `x` commits at index 4 with `{3,4}`; node 1 sees no unapplied conf
  change (committed 0), node 2 (holding indices 1–2) votes for it, `{1,2}` is a `C0`
  majority, and node 1 commits a different entry at index 4. Reproduction in the abstract
  model: `issues/raft-conf-lag-model/` (`python3 model.py 4 3 crash 3 5 2 2 simple
  trace-crash.txt`, which ends UNSAFE).
- **Expected**: the documentation requires a `Ready`'s entries and `HardState` to be
  persisted atomically (or the commit index first); or raft does not rely on the persisted
  commit index for the campaign guard.
- **How the proof handles it**: not reached (no conf change is ever applied in the verified
  scope). The reconfiguration work will assume atomic persistence (in the storage's spec).
  etcd's WAL writes the entry records then the state record before one fsync; a torn tail
  after a power loss could plausibly keep the entries and drop the state (not tested).
- **Possible fixes**: document atomic persistence in `doc.go` step 1; or persist the commit
  index before (with) the entries in etcd's WAL record order.
- **Found**: 2026-10-13, the same analysis as
  [raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md).
