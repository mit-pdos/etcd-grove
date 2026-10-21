---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/raft#300 pr closed: same root cause (HardState.Commit not persisted with the entries), different symptom (force-new-cluster drops a committed entry); closed, resolved on the etcd side
  - etcd-io/raft#234 issue closed: related, not this bug: split brain with a stalled apply; closed citing hasUnappliedConfChanges (assumes conf changes applied before the applied index moves)
---

# raft: entries persisted without their `HardState.Commit` can break membership safety

- **Status**: open (documentation precondition; plausibility only, not demonstrated on etcd).
  Upstream draft (with the `Advance` precondition):
  [raft-document-confchange-before-advance](raft-document-confchange-before-advance.md).
  The guard fix (`raft-conf-lag-model/guard-fix.md`) does not address it.
- **Where**: etcd-raft at the pinned revision: `hasUnappliedConfChanges` (`raft.go:990`)
  scans `(applied, committed]` with the *persisted* commit after a restart; `doc.go:74-76`
  (step 1 of handling a `Ready`) asks to write the entries, the `HardState` and the snapshot
  but does not require them to be persisted atomically.
- **What happens**: plain Raft treats the commit index as volatile; etcd-raft's election
  guard against unapplied conf changes makes it safety-relevant. A node may not campaign
  while a conf change lies in `(applied, committed]`, and after a restart `committed` is
  whatever the persisted `HardState` says. If the entries are durable but the new commit
  index is not, the node restarts with a configuration older than its committed log and a
  commit index low enough that the guard sees no unapplied conf change.
  The execution below is the abstract model's (`trace-crash.txt`), not a run of the Go code.
  The model's `crash` action is a simplification: it restarts a node with the commit index
  persisted before its last append, nothing applied, and the initial configuration.
  1. `C0 = {1,2,3}`. Node 3 leads term 1 with node 2's vote and appends its empty entry at
     index 1. It commits and applies `C1 = add 4` (index 2), then proposes `C2 = remove 2`
     (index 3). Node 2 holds indices 1–2.
  2. Node 1 receives indices 1–3 with `Commit = 2`, persists the entries, and crashes before
     the `HardState` with commit 2 is durable. It restarts with commit 0 and configuration
     `C0`.
  3. Node 3 replicates to node 4, commits `C2`, and applies it: `{1,3,4}`. It commits `x` at
     index 4 with `{3,4}`.
  4. Node 1 sees no conf change in `(0, 0]` and campaigns. Node 2, whose log is shorter,
     votes for it. `{1,2}` is a majority of `C0`. Node 1 wins term 2 and commits its empty
     entry at index 4 with node 2: a different entry at index 4.

  Reproduction in the abstract model: `issues/raft-conf-lag-model/` (`python3 model.py 4 3
  crash 3 5 2 2 simple trace-crash.txt`, which ends UNSAFE).

  Step 1 of handling a `Ready` asks for the entries and the `HardState` to be written, but not
  atomically:

  ```go
  // doc.go:75-77 (etcd-io/raft 40f8be7), step 1
  1. Write HardState, Entries, and Snapshot to persistent storage if they are // <-
  not empty. Note that when writing an Entry with Index i, any
  previously-persisted entries with Index >= i must be discarded.
  ```

  On restart the commit index comes from the persisted `HardState`, and the guard scans only
  up to it:

  ```go
  // raft.go:478-480, 2025-2029, 990-993 (etcd-io/raft 40f8be7)
  	if !IsEmptyHardState(hs) {
  		r.loadState(hs)
  // loadState:
  func (r *raft) loadState(state pb.HardState) {
  	if state.Commit < r.raftLog.committed || state.Commit > r.raftLog.lastIndex() {
  		r.logger.Panicf("%x state.commit %d is out of range [%d, %d]", r.id, state.Commit, r.raftLog.committed, r.raftLog.lastIndex())
  	}
  	r.raftLog.committed = state.Commit // <-
  // hasUnappliedConfChanges, before a campaign:
  func (r *raft) hasUnappliedConfChanges() bool {
  	if r.raftLog.applied >= r.raftLog.committed { // in fact applied == committed // <-
  		return false
  	}
  ```

  Writing the `HardState` first does not help: a commit index past the last persisted entry
  makes `loadState` panic on restart.
- **Expected**: the documentation requires a `Ready`'s entries and `HardState` to be
  persisted atomically (the commit index first does not work: see above); or raft does not
  rely on the persisted commit index for the campaign guard.
- **How the proof handles it**: not reached (no conf change is ever applied in the verified
  scope). The reconfiguration work will assume atomic persistence (in the storage's spec).
  etcd's WAL writes the entry records then the state record before one fsync; a torn tail
  after a power loss could plausibly keep the entries and drop the state (not tested).
- **Possible fixes**: document atomic persistence in `doc.go` step 1; or persist the commit
  index with the entries, atomically, in etcd's WAL.
- **Found**: 2026-10-13, the same analysis as
  [raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md). 2026-10-14:
  the model checker (`raft-conf-lag-model/checker/`) finds a 16-step execution by search
  (`raft-conf-lag-model/trace-check-crash-sms.txt`, two removals, the restarted node on
  `C0` wins with the removed node's vote): `notes/reconfiguration-model-check.md`.
