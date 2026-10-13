# raft: calling `Advance` before `ApplyConfChange`, which the documentation allows, breaks safety

- **Status**: open (documentation precondition; not reported upstream yet).
- **Where**: etcd-raft at the pinned revision (`etc/goose.py`):
  - the guards read raft's applied index, not the configuration in use:
    `hasUnappliedConfChanges` (`raft.go:978`, `990`: refuses to campaign with a conf entry in
    `(applied, committed]`), and the leader's `alreadyPending := r.pendingConfIndex >
    r.raftLog.applied` (`raft.go:1313`);
  - the applied index moves on `Advance` (`rawnode.go:482-494` replays the
    `MsgStorageApplyResp`, which calls `appliedTo`, `raft.go:1192-1195`), while the
    configuration switches only in `ApplyConfChange` (`applyConfChange`/`switchToConfig`,
    `raft.go:1939-1958`);
  - the documentation allows `Advance` before the entries are applied: `doc.go:100-102`
    (step 4, "This may be done at any time after step 1"; applying, including
    `ApplyConfChange`, is step 3) and `node.go:166-174` ("the application may call Advance
    while it is applying the commands").
- **What happens**: in the window between `Advance` and `ApplyConfChange` both guards treat
  the conf change as applied while the node still uses the old configuration. Two
  executions commit different entries at the same index:
  1. *Leader lag* (one window on the leader suffices). `C0 = {1,2,3}`, node 1 leads term 1.
     It commits `C1 = add 4` (index 2) with `{1,2}`, `Advance`s (applied = 2) without
     `ApplyConfChange`, so it is still on `C0`; proposes `C2 = remove 2` (index 3; accepted:
     `pendingConfIndex` 2 ≤ applied 2), commits it under `C0` with `{1,2}`; nodes 3 and 4
     receive indices 1–3 with `Commit = 3` and apply both changes (configuration
     `{1,3,4}`); node 1 commits `x` at index 4 under `C0` with `{1,2}`. Partitioned from
     `{1,2}`, node 3 wins term 2 with `{3,4}` (a majority of `{1,3,4}`; its applied =
     committed = 3, so no unapplied conf change) and commits its own entry at index 4.
  2. *Follower lag* (the planning pass's trace). `C1` adds 4, `C2` adds 5; node 1 receives
     both with `Commit = 3` and `Advance`s past them without applying either; `x` is
     committed at index 4 with `{3,4,5}`; node 1 (still `C0 = {1,2,3}`) wins term 2 with
     `{1,2}` and overwrites index 4.

  Reproduction (an abstract model of the protocol with apply-time configuration switching,
  `raft-conf-lag-model/model.py`; mode `lag` lets applied run ahead of `ApplyConfChange`,
  `faithful` does not):

      cd issues/raft-conf-lag-model
      python3 model.py 4 3 lag 3 5 2 2 simple trace-leaderlag.txt      # ends UNSAFE
      python3 model.py 4 3 faithful 3 5 2 2 simple trace-leaderlag.txt # refused at ('commit', 1, 3)

  (`trace-followerlag.txt` likewise.)

  **Go reproduction** on the real code at the pinned revision (40f8be7), public API only
  (`RawNode`: `Campaign`, `Propose`, `ProposeConfChange`, `Ready`, `Advance`,
  `ApplyConfChange`, `Step`; synchronous `MemoryStorage`, messages routed by hand):
  `raft-conf-lag-model/leaderlag_test.go`, `TestAdvanceBeforeApplyConfChangeLeaderLag`.
  Node 1's application calls `Advance` while holding back `ApplyConfChange` (doc.go step 4);
  the others apply before `Advance`. Node 4 joins empty and catches up from node 3; node 3's
  conflicting entry at index 4 is its empty leader entry. The test passes by asserting the
  violation:

      cp issues/raft-conf-lag-model/leaderlag_test.go <etcd-raft checkout>/
      cd <etcd-raft checkout> && go test -run TestAdvanceBeforeApplyConfChangeLeaderLag -v .
      ...
      SAFETY VIOLATION reproduced: index 4 committed as "x" (term 1) on node 1 and as "" (term 2) on node 3

  With node 1 applying before `Advance` (a control edit, not in the file) the violation does
  not occur: node 1 moves to `{1,3,4}` and `x` cannot commit with node 3 cut off.
- **Expected**: either the documentation states the precondition -- the conf changes of a
  `Ready`'s committed entries are applied (`ApplyConfChange`) before `Advance` (before the
  `MsgStorageApplyResp`, with asynchronous storage writes) -- or raft's guards track the
  configuration actually in use rather than the applied index.
- **A second consequence: a panic** (found 2026-10-13, reconfiguration stage A2). The same
  window lets a node campaign with its own removal committed but not yet applied; when the
  application then calls `ApplyConfChange`, the node stays a candidate outside the
  configuration (`switchToConfig` steps down only a removed *leader*, and only with
  `StepDownOnRemoval`). If the remaining voters grant it their votes it wins, and
  `becomeLeader` (`raft.go:942-943`, `pr := r.trk.Progress[r.id]; pr.BecomeReplicate()`)
  dereferences its missing `Progress`: a nil-pointer panic. Reproduction of the code path
  (internal API: `newTestRaft`, `applyConfChange`, `Step`):
  `raft-conf-lag-model/removed_candidate_test.go`, `TestRemovedCandidateWinsAndPanics`, which
  passes by recovering the panic:

      cp issues/raft-conf-lag-model/removed_candidate_test.go <etcd-raft checkout>/
      cd <etcd-raft checkout> && go test -run TestRemovedCandidateWinsAndPanics -v .
      ...
      removed_candidate_test.go:47: PANIC reproduced: runtime error: invalid memory address or nil pointer dereference

  The public-API route is the leader-lag test's: `Advance` past the committed removal, a
  campaign (no unapplied conf change in `(applied, committed]`), then `ApplyConfChange`. Not
  demonstrated end to end through `RawNode`. The proof excludes it by premise:
  `raft.switchToConfig.spec` and `raft.applyConfChange.spec` require a candidate to stay a
  voter, and `RawNode.ApplyConfChange.spec` (`CCApplies`) that the node stays a voter.
- **How the proof handles it**: today no node ever applies a conf change (the verified
  scope has a fixed voter set: `ownRaftPhys cfg`, `γ.reCfg = cfg` in `raft.Step.spec`,
  `HnoConfChange` in `ownRaftLog`). The reconfiguration work will state the precondition on
  `ApplyConfChange`/`Advance` (notes/STATUS.md, "Reconfiguration"). Under it (and atomic
  persistence, see [raft-commit-lost-with-entries-kept](raft-commit-lost-with-entries-kept.md))
  a proof sketch of safety holds: any two conf entries in a log imply its commit index covers
  the first; a campaigning node or a leader has at most one conf entry beyond its applied
  index; so the configurations of a committer and a winner are adjacent (overlapping
  quorums) or the winner's committed prefix covers the entry.
- **Possible fixes**: document the precondition in `doc.go` (step 4) and on `Node.Advance`/
  `RawNode.Advance`; or have raft remember the index of the last applied configuration and
  use it in `hasUnappliedConfChanges` and the leader's pending check. etcd's server waits
  for apply before `Advance` on followers and candidates (`etcdserver/raft.go:296-331`, whose
  comment names this hazard) but not on the leader (`server.go:1917-1925`): the leader-lag
  execution may be reachable in etcd (slow apply goroutine plus a partition; not
  demonstrated).
- **Found**: 2026-10-13, analysing the reconfiguration stage B0 (apply-time configurations)
  for the protocol model; checked by replay in the abstract model and reproduced by the Go
  test above (the model's exhaustive search covered only depth 10–11: no evidence beyond the
  traces).
