# raft-snapshot-during-apply-stale-confchange

- **Finding**: `issues/raft-snapshot-during-apply-stale-confchange.md`
- **Target**: etcd-io/raft, `main` (raftpb on protobuf-go v2; the finding's 40f8be7 has the same code)
- **Branch**: `fix/raft-snapshot-during-apply-stale-confchange` in `~/etcd-fixes/raft-snapshot-during-apply-stale-confchange` (commit c65d182b8), pushed 2026-10-18 to `upamanyus/etcd-raft`
  (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-snapshot-during-apply-stale-confchange`), the branch the links in `issue.md` name.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections. The fix is a design choice; the issue asks the maintainers which they prefer,
and the PR is the smallest of the options.

## Duplicates checked (2026-10-16)

Searches on `repo:etcd-io/raft`: `snapshot ApplyConfChange` (one hit, #8, closed PR "support asynchronous storage
writes", unrelated), `restore snapshot conf change applying` (none), `ApplyConfChange stale` (none). No duplicate.
Related findings in this repository, not reported here: `raft-advance-before-applyconfchange`,
`raft-track-confchange-application`, `raft-document-confchange-before-advance`.

## Re-check at the base

Unchanged since 40f8be7: `node.run` steps `recvc` while `advancec` is set (`node.go:394-399`, `435-446`);
`restore` restores a snapshot above the commit index whatever `applying`/`applied` are and resets the tracker
(`raft.go:1860-1942`); `applyConfChange` applies `cc` to `r.trk` with no index (`raft.go:1951-1971`).

## Verification

`TestRawNodeSnapshotDuringConfChangeApply` (in `rawnode_test.go`, after `TestRawNodeRestartFromSnapshot`) is the
issue's example: follower 2 of `{1,2,3}` steps a `MsgApp` committing "add 4" at index 1, takes the `Ready`, appends
its entries, then (`snapBeforeApply=true` only) steps a `MsgSnap` at index 2 with voters `{1,2,3}`, calls
`ApplyConfChange("add 4")` and `Advance`, then steps the `MsgSnap` (again); it asserts voters `[1 2 3]`. The second
step stands for the leader resending an ignored snapshot; at the base it is ignored in the failing case (index 2
is already committed), so the base behaviour is the issue's.

- At the base (fix reverted, test kept): `go test . -run 'TestRawNodeSnapshotDuringConfChangeApply$'` fails,
  `snapBeforeApply=true`: expected `[1 2 3]`, actual `[1 2 3 4]`; `snapBeforeApply=false` passes.
- With the fix: the test passes; `go test . ./confchange/ ./tracker/` ok (includes the datadriven interaction
  tests); `gofmt -l raft.go rawnode_test.go` empty; `go vet . ./confchange/ ./tracker/` clean (go1.26.9 linux/amd64).
- Joint variant, not on the branch (an overlay test, `ConfChangeV2` `JointExplicit` "add 4" at index 1, snapshot at
  index 2 in the joint configuration `(1 2 3 4)&&(1 2 3)`): at the base `ApplyConfChange` panics "config is already
  joint"; with the fix the follower ends in `voters=(1 2 3 4)&&(1 2 3)`.

Not run: `rafttest`, `quorum`, `raftpb`, etcd's tests, `make verify`. Not reproduced with a real leader or on a
cluster: the leader's messages are built by hand. That the leader resends an ignored snapshot is by reading
(`raft.go:1611-1628`: after `ReportSnapshot` the leader probes; the follower's reject sends `Next` below the
leader's first index, so `sendAppend` sends a snapshot again), not tested end to end.

## etcd

etcd's raft loop (`server/etcdserver/raft.go:297-331` at etcd `main` b25719d10) makes a follower whose `Ready` has a
conf change wait for the apply goroutine before `Advance`; meanwhile `node.run` keeps stepping messages from the
transport, `MsgSnap` included, and the apply goroutine calls `ApplyConfChange` (`server.go:2002-2024`) with etcd's
membership not yet replaced by the snapshot (which comes in the next `Ready`). So etcd can reach it: a follower
applying a membership change while the leader sends it a snapshot (it is behind the leader's compacted log). Not
reproduced on etcd. A client cannot cause it on its own: it needs a membership change (`MemberAdd`/`MemberRemove`,
root when auth is on) and a follower lagging past the leader's compaction point at that moment; etcd uses v1 conf
changes only, so the outcome is a wrong configuration on one follower, not the joint panic. Not a security report.

## If a reviewer asks

- Cost: a follower that receives a snapshot between `Ready` and `Advance` (or, with `AsyncStorageWrites`, while
  an apply is outstanding) ignores it and the leader sends it again: one more snapshot transfer. The follower is
  behind the leader's compacted log, so its commit index does not move until it restores a snapshot, and its
  applying catches up with it; the retry then succeeds.
- Narrower: ignore the snapshot only when `(applied, applying]` holds a conf change entry. Needs raft to track that
  (it does not for followers) or to read those entries in `restore`.
- Alternative: let `ApplyConfChange` skip a change that a restored snapshot covers. `ApplyConfChange` has no index,
  and counting the conf changes in the window fails when the application already called it before the snapshot
  arrived; raft would have to track which entry each call is for (an API change: an index argument, or tracking
  the conf entries it hands out, as a prototype here did behind a `Config` flag).
- Alternative: document that `Step` must not be called between `Ready` and `Advance`. `Node` does it itself
  (`node.run`), and `doc.go` puts no condition on `Node.Step`.
- The check is after the fast-forward path (`matchTerm`), so a snapshot whose index and term are in the log still
  advances the commit index during an apply, as before: its entries are then applied in order through `Ready`.

## check.py

Clean but for one WARN, decided: the comment added in `restore` is kept, since it says why the snapshot is ignored
(the pending `ApplyConfChange` calls) and that the leader retries, neither of which the condition shows.
