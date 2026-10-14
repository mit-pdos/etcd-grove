# raft: track which conf changes have been applied, so that Advance before ApplyConfChange is safe

## Summary

raft's guards against overlapping configuration changes (`hasUnappliedConfChanges` before a
campaign, `pendingConfIndex > applied` before accepting a conf change proposal) read the
applied index, which `Advance` (or, with `AsyncStorageWrites`, the `MsgStorageApplyResp`)
moves. The configuration in use changes only in `ApplyConfChange`. When an application calls
`Advance` before `ApplyConfChange`, which `doc.go` and `Node.Advance` allow, the guards
think a conf change is applied while the node still uses the previous configuration, and
two different entries can be committed at the same index (#TODO, the documentation issue,
with a reproduction through `RawNode`). This issue proposes a code change that makes the
guards follow the conf changes actually applied, so that the documented permission holds.
The same mechanism also fixes a related bug: a snapshot restored while a `Ready`'s conf
change is being applied makes the later `ApplyConfChange` call apply it on top of the
snapshot's configuration (#TODO).

We found these while formally verifying etcd-raft's reconfiguration. A prototype patch with
tests is attached (`guard-fix.patch`, against 40f8be730b18).

## What happens

References are to `main` at 40f8be730b18.

- `hasUnappliedConfChanges` (`raft.go:990-1020`) scans `(applied, committed]` for a conf
  change; `hup` (`raft.go:978`) refuses to campaign if it finds one.
- `stepLeader`, `MsgProp` (`raft.go:1313`): `alreadyPending := r.pendingConfIndex > r.raftLog.applied`.
- Auto-leave (`raft.go:740`, `appliedTo`): `newApplied >= r.pendingConfIndex`.
- `applied` moves in `appliedTo`, from the `MsgStorageApplyResp` that `Advance` steps
  (`rawnode.go:482-494`, `raft.go:1192-1196`) or that the application's apply thread
  returns with `AsyncStorageWrites`.
- `ApplyConfChange` (`rawnode.go:112`, `raft.applyConfChange`, `raft.go:1939-1958`) switches
  the configuration; it does not know which entry it applies.

So between `Advance` and `ApplyConfChange` a leader accepts a second conf change while it
still uses the configuration before the first, and a node campaigns with a committed conf
change it has not applied (including its own removal, which then crashes in
`becomeLeader`). With `AsyncStorageWrites`, nothing orders `ApplyConfChange` (which must run
on the goroutine that owns the `RawNode`) against stepping the apply thread's response, so
the window is natural there. Auto-leave has the same gap: if `Advance` precedes the
`ApplyConfChange` that enters a joint configuration, `appliedTo` saw the old configuration
and the leader does not start leaving the joint one until some later entry is applied.

## How to reproduce

`TestAdvanceBeforeApplyConfChangeLeaderLag` and `TestRemovedCandidateWinsAndPanicsRawNode`
(see #TODO). The patch's `confchange_lag_test.go` runs the same executions with the new
option, in both storage modes; with the option off (one line in the test's config) every
test fails on the current behaviour:

```
--- FAIL: TestConfChangeLagLeaderLag/sync: C2 should have been refused (replaced by an empty normal entry), got {Term:1 Index:3 Type:EntryConfChange ...}
--- FAIL: TestConfChangeLagRemovedCandidate/async: node 3 campaigned with its removal unapplied: StateCandidate
--- FAIL: TestConfChangeLagAutoLeave: node 1 config voters=(1 2)&&(1 2 3), want voters=(1 2)
--- FAIL: TestConfChangeLagSnapshotDuringApply/simple: configuration voters=(1 2 3 4) after the stale conf change, want the snapshot's voters=(1 2 3)
panic: config is already joint   (TestConfChangeLagSnapshotDuringApply/joint)
```

## Expected

The guards hold whatever the application's timing of `Advance` (or of the apply response)
relative to `ApplyConfChange`, as `doc.go` step 4 promises; or, if that is not wanted, the
precondition is documented (#TODO).

## Proposed fix

raft records the index of every conf change entry it hands to the application and matches
each `ApplyConfChange` call with the oldest one; the guards use the result.

- `raft.confChangesToApply []uint64`: `RawNode.acceptReady` appends the index of each conf
  change entry of `rd.CommittedEntries` (which is also what `MsgStorageApply` carries);
  `applyConfChange` pops the front.
- `confApplied()`: the applied index, or the index before the oldest pending conf change if
  that is at or below it. The configuration in use reflects exactly the conf entries up to
  it.
- `hasUnappliedConfChanges` returns true while `confChangesToApply` is nonempty (then scans
  as before); the leader's check is `pendingConfIndex > confApplied()`; the auto-leave check
  uses `confApplied()` and is also made from `applyConfChange` when the entry was already
  below the applied index.
- Entries appended by `Bootstrap` are already applied by it and are not queued; an
  `ApplyConfChange` call matching the next of them (`AddNode` of that peer) is taken as for
  it, and the first call that does not match shows the application skips them (raft's own
  `rafttest` harness and `TestNodeStart` never pass them to `ApplyConfChange`; etcd does).
- `restore` records the snapshot index; an `ApplyConfChange` call for a queued entry at or
  below it is ignored, since the snapshot's `ConfState` reflects it.

The contract this needs: the application calls `ApplyConfChange` exactly once per conf
change entry it receives, in log order, and for one it rejects, or whose effect its restored
state already reflects, it passes a change with `NodeId` zero (`confchange` ignores those,
`confchange.go:152-156`), as `doc.go:94-98` already says. Two existing usages break it, so
the prototype makes the behaviour opt-in, `Config.TrackConfChangeApplication`:

- `Node.ApplyConfChange` and `RawNode.ApplyConfChange` say a rejected change must not be
  passed at all (contradicting `doc.go`).
- etcd builds its raft `ConfState` at restart from its backend's membership, which is ahead
  of raft's applied index (the WAL snapshot), and skips `ApplyConfChange` for the replayed
  conf entries below its consistent index (`etcdserver/server.go`, `applyConfChange`, "We
  don't validate the configuration change when `shouldApplyV3` is false, so we shouldn't
  apply it to raft either"). Under the contract, it would pass a zero-`NodeId` change there.

A conf change entry that is never passed to `ApplyConfChange` blocks campaigning and
further conf changes on that node (liveness, not safety); with the option off nothing
changes. An alternative is an explicit API (`ApplyConfChangeAt(index, cc)`), which makes the
matching and the bootstrap rule unnecessary.

Results with the patch: `go test ./...` passes; with the option forced on for every test of
the package, `go test ./...` still passes (the bootstrap rule is what makes `rafttest` and
`TestNodeStart` pass); `-race` passes.

What it does not address: the documentation of atomic persistence of entries and
`HardState` (#TODO); a node that joins with an empty `ConfState` while the initial
configuration is only in an index-0 snapshot (#TODO).
