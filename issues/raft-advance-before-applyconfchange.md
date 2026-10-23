---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/etcd#4203 issue closed: related, flagged: asked in 2016 whether a Ready's conf change must be applied before Advance (maintainer: 'probably fair'); closed by etcd-io/etcd#4049, whose Advance comment allows Advance while applying without that exception; the safety consequence was not raised (maintainer called delaying a conf change apply safe)
  - etcd-io/raft#80 issue open: related, not this bug: the pendingConfIndex > applied proposal check gives false positives; proposes tracking the configuration explicitly
  - etcd-io/raft#234 issue closed: related, not this bug: split brain with a stalled apply; closed citing hasUnappliedConfChanges (assumes conf changes applied before the applied index moves)
  - etcd-io/raft#456 issue open: related, not this bug: the TLA+ spec lacks the hasUnappliedConfChanges guard; says the Go code is safe
  - etcd-io/etcd#12136 issue closed: related, not this bug: pendingConfIndex vs applied with AutoLeave (liveness), fixed by etcd-io/etcd#12137
  - etcd-io/raft#469 pr open: related, not this bug: adds the unapplied-conf-change campaign guard to the TLA+ spec
candidate: issues/upstream/raft-advance-before-applyconfchange/
---

# raft: calling `Advance` before `ApplyConfChange`, which the documentation allows, breaks safety

- **Status**: open (documentation precondition). Upstream candidate (2026-10-21): the documentation fix,
  `issues/upstream/raft-advance-before-applyconfchange/` (raft PR, documentation only; the reproduction
  `TestNodeAdvanceBeforeApplyConfChange` through `Node` on etcd-io/raft `main` 1931ff5be, three nodes), with
  etcd's leader change as a separate candidate on hold,
  `issues/upstream/etcd-leader-advance-before-applyconfchange/`; tracking (b) recorded there as an alternative
  not taken. Earlier drafts: `raft-document-confchange-before-advance.md` (document the
  precondition; deleted 2026-10-23 as a duplicate of this candidate, in git history) and
  [raft-track-confchange-application](nonissues/raft-track-confchange-application.md) (the guard fix,
  prototyped with tests in `raft-conf-lag-model/guard-fix.patch`, notes in
  [guard-fix.md](raft-conf-lag-model/guard-fix.md)); etcd's leader path:
  [etcd-leader-advance-before-applyconfchange](etcd-leader-advance-before-applyconfchange.md)
  (unconfirmed).
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

  In execution 1, `C2` passes the leader's check because `pendingConfIndex` (2) is not above
  applied (2), and node 3 may campaign because its applied index equals its commit index. The
  guards read `applied`; `becomeLeader` assumes the node has a `Progress` (the panic below):

  ```go
  // raft.go:978-981, 990-993, 1313, 942-943 (etcd-io/raft 40f8be7)
  // hup (before campaigning):
  	if r.hasUnappliedConfChanges() {
  		r.logger.Warningf("%x cannot campaign at term %d since there are still pending configuration changes to apply", r.id, r.Term)
  		return
  	}
  	// ...
  func (r *raft) hasUnappliedConfChanges() bool {
  	if r.raftLog.applied >= r.raftLog.committed { // in fact applied == committed // <-
  		return false
  	}
  	// ... scan (applied, committed] for EntryConfChange/EntryConfChangeV2
  // stepLeader, MsgProp:
  				alreadyPending := r.pendingConfIndex > r.raftLog.applied // <-
  // becomeLeader:
  	pr := r.trk.Progress[r.id] // <-
  	pr.BecomeReplicate()
  ```

  The documentation allows `Advance` before step 3's `ApplyConfChange`:

  ```go
  // doc.go:94-103 (etcd-io/raft 40f8be7)
  If any committed Entry has Type EntryConfChange, call Node.ApplyConfChange()
  to apply it to the node. The configuration change may be cancelled at this point
  by setting the NodeId field to zero before calling ApplyConfChange
  (but ApplyConfChange must be called one way or the other, and the decision to cancel
  must be based solely on the state machine and not external information such as
  the observed health of the node).

  4. Call Node.Advance() to signal readiness for the next batch of updates. // <-
  This may be done at any time after step 1, although all updates must be processed // <-
  in the order they were returned by Ready.
  ```

  ```go
  // node.go:167-174 (etcd-io/raft 40f8be7), Node.Advance
  	// It prepares the node to return the next available Ready.
  	//
  	// The application should generally call Advance after it applies the entries in last Ready.
  	//
  	// However, as an optimization, the application may call Advance while it is applying the // <-
  	// commands. For example. when the last Ready contains a snapshot, the application might take
  	// a long time to apply the snapshot data. To continue receiving Ready without blocking raft
  	// progress, it can call Advance before finishing applying the last ready.
  ```

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

  The public-API route: `Advance` past the committed removal, a campaign (no unapplied conf
  change in `(applied, committed]`), then `ApplyConfChange`. Demonstrated end to end through
  `RawNode` (2026-10-14): `raft-conf-lag-model/removed_candidate_rawnode_test.go`,
  `TestRemovedCandidateWinsAndPanicsRawNode` (needs `leaderlag_test.go` beside it):

      removed_candidate_rawnode_test.go:60: node 3: StateCandidate, config voters=(1 2)
      removed_candidate_rawnode_test.go:63: PANIC reproduced: runtime error: invalid memory address or nil pointer dereference

  The proof excludes it by premise:
  `raft.switchToConfig.spec` and `raft.applyConfChange.spec` require a candidate to stay a
  voter, and `RawNode.ApplyConfChange.spec` (`CCApplies`) that the node stays a voter.
- **How the proof handles it**: today no node ever applies a conf change (the verified
  scope has a fixed voter set: `ownRaftPhys cfg`, `γ.reCfg = cfg` in `raft.Step.spec`,
  `HnoConfChange` in `ownRaftLog`). The reconfiguration work will state the precondition on
  `ApplyConfChange`/`Advance` (notes/status-history.md, "Reconfiguration"). Under it (and atomic
  persistence, see [raft-commit-lost-with-entries-kept](nonissues/raft-commit-lost-with-entries-kept.md))
  a proof sketch of safety holds: any two conf entries in a log imply its commit index covers
  the first; a campaigning node or a leader has at most one conf entry beyond its applied
  index; so the configurations of a committer and a winner are adjacent (overlapping
  quorums) or the winner's committed prefix covers the entry.
- **Possible fixes**: document the precondition in `doc.go` (step 4) and on `Node.Advance`/
  `RawNode.Advance`; or have raft track which conf changes have been passed to
  `ApplyConfChange` and use that in `hasUnappliedConfChanges` and the leader's pending check.
  The second is prototyped (`raft-conf-lag-model/guard-fix.patch`, opt-in
  `Config.TrackConfChangeApplication`; [guard-fix.md](raft-conf-lag-model/guard-fix.md)):
  with it both executions above are refused, in synchronous and asynchronous storage modes,
  and `go test ./...` passes. It is opt-in because applications that skip `ApplyConfChange`
  for rejected changes (as `Node.ApplyConfChange` tells them to, contradicting `doc.go`) or
  for replayed entries (etcd after a restart) would lose liveness.
  etcd's server waits for apply before `Advance` on followers and candidates
  (`etcdserver/raft.go:297-324`, whose comment names this hazard) but not on the leader
  (`raft.go:325-331`; the conf change is applied later, `server.go:1917-1925`), and its
  membership checks do not serialize concurrent changes: the leader-lag execution may be
  reachable in etcd (slow apply loop, a concurrent membership change, a partition; not
  demonstrated): [etcd-leader-advance-before-applyconfchange](etcd-leader-advance-before-applyconfchange.md).
- **Found**: 2026-10-13, analysing the reconfiguration stage B0 (apply-time configurations)
  for the protocol model; checked by replay in the abstract model and reproduced by the Go
  test above (the model's exhaustive search covered only depth 10–11: no evidence beyond the
  traces). 2026-10-14: a Go checker of the same model (`raft-conf-lag-model/checker/`)
  finds the violation by search, in shorter executions (leader completeness at depth 18;
  state machine safety at depth 17 with three nodes and two removals,
  `raft-conf-lag-model/trace-check-lag-sms.txt`), and none in the faithful mode at the
  bounds it searched exhaustively: `notes/reconfiguration-model-check.md`.
