# A prototype of the guard fix for raft-advance-before-applyconfchange

`guard-fix.patch` (`git diff` against etcd-io/raft `40f8be730b18`, the revision
`etc/goose.py` pins) makes raft's two guards against overlapping configuration changes go
by the conf changes the application has actually passed to `ApplyConfChange`, not by the
applied index. It is opt-in (`Config.TrackConfChangeApplication`), for the reasons in
"Why opt-in" below. Written 2026-10-14 (parallel session, task 2 of
`notes/parallel-work.md`). The issue it fixes:
[raft-advance-before-applyconfchange](../raft-advance-before-applyconfchange.md).

Apply and test:

    cp -r .lake/go-src/etcd-raft /tmp/raft && cd /tmp/raft
    git apply <repo>/issues/raft-conf-lag-model/guard-fix.patch
    go test ./...                                  # all packages pass
    go test -run TestConfChangeLag -v .            # the new tests

(go1.26.2; the module needs nothing newer.) The patch also applies on top of
`readindex-singleton-fix.patch` (different hunks of `raft.go`).

## What the patch does

How raft learns which configuration is in use. `ApplyConfChange(cc)` carries no index, so
raft counts: it records the index of every conf change entry it hands to the application
and matches each `ApplyConfChange` call with the oldest one (the application applies
committed entries in log order, `doc.go` step 4 and `node.go`'s `Ready` comment).

- `raft.confChangesToApply []uint64` (new): the indexes of the conf change entries handed
  out (`Ready.CommittedEntries`, which is also what `MsgStorageApply` carries) and not yet
  passed to `ApplyConfChange`. `RawNode.acceptReady` appends to it (the one place both
  `RawNode.Ready` and `node.run` hand out committed entries); `raft.applyConfChange` pops
  the front.
- `raft.confApplied()` (new): the applied index, or the index before the oldest pending
  conf change if that one is at or below the applied index. The configuration in use
  (`r.trk.Config`) reflects every conf change entry up to `confApplied()` and no later one.
- `hasUnappliedConfChanges` (pinned `raft.go:990`) returns true when `confChangesToApply` is
  nonempty, before its scan of `(applied, committed]` (unchanged). So a node campaigns only
  when every committed conf change entry has been passed to `ApplyConfChange`.
- The leader's check (pinned `raft.go:1313`) is
  `alreadyPending := r.pendingConfIndex > r.confApplied()`.
- Auto-leave (pinned `raft.go:740`, `appliedTo`) is factored into `maybeAutoLeave`, which
  compares `confApplied()` with `pendingConfIndex`. It is also called from
  `applyConfChange` when the entry just applied was already below the applied index: if
  `Advance` came first, `appliedTo` ran while the old configuration was in use and could not
  start leaving the joint configuration the entry enters. (Pinned code has the same gap: the
  leader stays joint until some later entry is applied; `TestConfChangeLagAutoLeave` fails
  there with `voters=(1 2)&&(1 2 3)`.)
- Bootstrap. `RawNode.Bootstrap` (`StartNode`) appends the peers' conf entries and applies
  them itself; some applications never pass them to `ApplyConfChange` (the package's own
  `rafttest` harness and `TestNodeStart`), others do (etcd, and `doc.go` says to). They are
  not queued (`raft.bootstrapLastIndex`), and an `ApplyConfChange` call that matches the next
  bootstrap entry (`AddNode` of that peer) is taken as for it (`raft.bootstrapConfChanges`);
  the first call that does not match shows the application skips them, and the list is
  dropped. Without this, raft's own tests hang (no node can ever campaign).
- Snapshots. `raft.restore` records the snapshot index (`raft.confRestoredIndex`); an
  `ApplyConfChange` call for a queued entry at or below it is ignored (returns the current
  `ConfState`), since the snapshot's `ConfState` already reflects it. This fixes a second
  bug that the queue makes fixable: [raft-snapshot-during-apply-stale-confchange](../raft-snapshot-during-apply-stale-confchange.md).
- Documentation: `Config.TrackConfChangeApplication`'s comment states the contract;
  `doc.go` step 4, `Node.Advance`, `Node.ApplyConfChange` and `RawNode.ApplyConfChange`
  state the precondition that holds without the flag (conf changes applied before `Advance`
  / before stepping the `MsgStorageApplyResp`).

With the flag off nothing changes: the queue stays empty, so `confApplied()` is the applied
index and every other change is inert.

## Tests (`confchange_lag_test.go`, in the patch)

Public `RawNode` API, `MemoryStorage`, messages routed by hand; each test with a lagging
application (it calls `Advance`, or delivers the `MsgStorageApplyResp`, before
`ApplyConfChange`), most in both storage modes:

| Test | Shows (flag on) |
|---|---|
| `TestConfChangeLagLeaderLag/{sync,async}` | `leaderlag_test.go`'s execution: `C2 = remove 2` is refused (index 3 becomes an empty normal entry) while the leader has not applied `C1`; node 3 then stays on `{1,2,3,4}` and cannot win with `{3,4}`; no index is committed differently on any two nodes |
| `TestConfChangeLagLiveness/{sync,async}` | once the leader applies `C1`, `C2` is accepted and commits (`voters=(1 3 4)`); a lagging follower holding `C2` back cannot campaign |
| `TestConfChangeLagRemovedCandidate/{sync,async}` | a follower that `Advance`d past its own committed removal cannot campaign; after `ApplyConfChange` it is unpromotable; no panic |
| `TestConfChangeLagAutoLeave` | a lagging leader entering a joint configuration with auto-leave still leaves it |
| `TestConfChangeLagRestart` | after a restart the replayed conf entry blocks campaigning until it is passed to `ApplyConfChange` again |
| `TestConfChangeLagSnapshotDuringApply/{simple,joint}` | a stale `ApplyConfChange` after a snapshot restore is ignored (pinned: `voters=(1 2 3 4)` instead of the snapshot's `(1 2 3)`; panic "config is already joint") |

Results, 2026-10-14, go1.26.2:

- Patched, flag as the tests set it: `go test ./...` passes (all six packages), also with
  `-race`; the six `TestConfChangeLag*` tests (ten cases) pass.
- Patched, with tracking forced on for every test of the package (`trackConfChanges: true`
  in `newRaft`, not in the patch): `go test ./...` passes. So the existing tests, including
  `rafttest`'s datadriven interaction tests and the `node` tests, are compatible with the
  contract, given the bootstrap rule above (before that rule, `TestNodeStart` and
  `rafttest` hung).
- Patched, flag off in `confchange_lag_test.go`: every `TestConfChangeLag*` test fails, each
  on the pinned behaviour (C2 accepted at index 3; node 3 campaigns with its removal
  unapplied; stuck at `voters=(1 2)&&(1 2 3)`; stale conf change applied; panic "config is
  already joint").
- `leaderlag_test.go` itself (unchanged) still reproduces the violation on the patched code,
  since it does not set the flag. With `TrackConfChangeApplication: true` added to its
  `Config` it fails before the end, which is the flipped assertion:

      leaderlag_test.go:230: C2 was not accepted as a conf change at index 3: {Term:1 Index:3 Type:EntryNormal Data:[]}

## Does it close the counterexample?

The lag class, yes, for an application that keeps the contract (one `ApplyConfChange` call
per handed-out conf entry, in order). With the flag, the guards' answers depend only on
which conf entries have been passed to `ApplyConfChange`: `hasUnappliedConfChanges` is
"some committed conf entry is not yet applied to the configuration in use" and the leader's
check is "some conf entry up to `pendingConfIndex` is not yet applied". These are exactly
the guards of an application that applies before `Advance` (the model's `faithful` mode,
with `applied` read as `confApplied()`), whatever the timing of `Advance` or of the
`MsgStorageApplyResp`. Every other safety-relevant use of the configuration (vote tally,
commit quorum, `promotable`) already reads the configuration in use. Both traces
(`trace-leaderlag.txt`, `trace-followerlag.txt`) are cut at the step the faithful mode
refuses: the leader's second proposal, or the lagging node's campaign. The removed-candidate
panic needs a campaign with the removal committed and not applied; that campaign is refused.
A pre-candidate that wins its pre-vote campaigns without re-checking (`stepCandidate`), but
its commit index cannot grow while it is a pre-candidate (a `MsgApp` of its term makes it a
follower first), so nothing new can become unapplied.

What it does not close:

- **The joiner with an empty `ConfState`** ([raft-joiner-empty-confstate](../raft-joiner-empty-confstate.md),
  found by the B1 review): `leaderlag_test.go`'s node 4 starts with empty storage and ends at
  `voters=(4)`; it could win alone. The guard fix does not help (node 4 does apply its
  changes; its configuration is wrong because its starting point is). The original
  violation does not depend on it (node 3, whose configuration is right, wins with node 4's
  vote), but its control claim does. In `confchange_lag_test.go` node 4 therefore starts
  from `C0`'s `ConfState`, as that issue's fix asks, so the tests' safety checks are not
  vacuous because of it; in the leader-lag test node 4 never applies anything (node 1, on
  `C0`, does not replicate to it, and node 3 never leads).
- **Non-atomic persistence** ([raft-commit-lost-with-entries-kept](../raft-commit-lost-with-entries-kept.md)):
  the crash trace loses `HardState.Commit`, so the scan of `(applied, committed]` misses the
  conf entry; the queue is in memory and empty after the restart. Untouched.
- **A restart with `Config.Applied` past a conf entry newer than the stored `ConfState`**
  (the restart analogue in raft-joiner-empty-confstate): entries up to `Applied` are never
  handed out, so never queued; the application's restart contract.
- **Applications that break the contract.** One that skips `ApplyConfChange` for a conf
  change it rejects (which `Node.ApplyConfChange` and `RawNode.ApplyConfChange` tell it to
  do, contradicting `doc.go` step 3) or for replayed entries its state already reflects
  (etcd, below) leaves an entry queued forever: the node never campaigns again and, as
  leader, never accepts another conf change. Liveness, not safety; it is why the patch is
  opt-in.
- **Safety of the faithful mode itself**: that rests on the paper proof
  (`notes/reconfiguration-safety.md`) and on the model's shallow search, not on this patch.

## Asynchronous storage writes

With `AsyncStorageWrites` the applied index moves when the raft goroutine steps the
`MsgStorageApplyResp` that the apply thread returns after applying a `MsgStorageApply`
(`raft.go:1192-1196`). `ApplyConfChange` must run on the goroutine that owns the `RawNode`,
not on the apply thread, and nothing documents its order against that response (the
`AsyncStorageWrites` comment, `raft.go:150-184`, only says responses are delivered after
the storage write). An apply thread that applies a conf change to its state machine, hands
it to the raft goroutine and delivers the response opens the same window as `Advance`
before `ApplyConfChange`, and the response may well be stepped first. The pinned code is
exposed exactly as in synchronous mode: the `async` subtests fail without the flag in the
same way.

With the flag the window is harmless. `MsgStorageApply` carries `rd.CommittedEntries`, which
`acceptReady` has already queued, so the queue does not depend on when, or in what order
relative to `ApplyConfChange`, the response is stepped. The `async` subtests drive
exactly the bad order (node 1 or node 3 async, the response routed before
`ApplyConfChange`). Two async-specific points checked:

- `MsgStorageApplyResp` has term 0 (a local message), so it is never dropped as stale; its
  handling (`appliedTo`) is unchanged apart from the auto-leave check.
- Several `MsgStorageApply` messages may be outstanding (their entries are within
  `MaxCommittedSizePerReady`); the queue covers all of them, in order.

## Restarts

On restart (`newRaft`) the queue is empty. raft's configuration is `InitialState`'s
`ConfState`, its applied index `Config.Applied` (or the snapshot index), and it hands out
`(applied, committed]` again. Every conf entry in that range is queued when handed out.

- `MemoryStorage`-style applications (the `ConfState` is the snapshot's, the entries after
  it are re-applied): the application passes the replayed conf entries to
  `ApplyConfChange` again, which re-derives the configuration; `TestConfChangeLagRestart`.
- Applications whose stored `ConfState` is ahead of the applied index (etcd, below) must
  pass a no-op (`NodeId` zero) for the replayed entries their `ConfState` already reflects.
  Re-applying them instead would be wrong for non-idempotent changes (entering a joint
  configuration twice panics).
- Until the replayed conf entries are passed to `ApplyConfChange` the node cannot campaign,
  which is the pinned behaviour too (they are in `(applied, committed]` until `Advance`).

## Why opt-in

A default-on change would turn two existing, documented usages into permanent loss of
availability:

1. `Node.ApplyConfChange`/`RawNode.ApplyConfChange` say that an application rejecting a
   change must not call `ApplyConfChange` (`node.go:179-187`, `rawnode.go:109-111`), while
   `doc.go:94-98` says it must call it with the `NodeId` zeroed. The contract needs the
   latter.
2. etcd skips `ApplyConfChange` for the conf entries it replays after a restart below its
   consistent index (`server/etcdserver/server.go:2018-2024`: "We don't validate the
   configuration change when `shouldApplyV3` is false, so we shouldn't apply it to raft
   either"), because its raft configuration on restart is built from the backend's
   membership (`bootstrap.go:107-119`, `buildConfStateFromV3store`), which is already past
   them, while raft's applied index starts at the older WAL snapshot (`raftConfig` sets no
   `Applied`). With the default on, every etcd member that restarts with a conf entry
   between its WAL snapshot and its consistent index (the usual case for up to
   `SnapshotCount` entries after a membership change) would never campaign again. To adopt
   the flag etcd would call `s.r.ApplyConfChange` with `NodeId` zero in that branch
   instead of skipping it (code reading; the etcd at the pinned revision uses raft v3.7 with
   protobuf getters, which this raft revision does not build against, so this was not run).

An index-carrying API (`ApplyConfChangeAt(index, cc)`) would make the matching explicit and
the bootstrap rule unnecessary, at the cost of a new method; the counting scheme keeps the
API.

## Other findings while doing this

- `TestRemovedCandidateWinsAndPanicsRawNode` (`removed_candidate_rawnode_test.go`, needs
  `leaderlag_test.go`): the removed-candidate panic, end to end through `RawNode` on the
  pinned code (previously only shown with the internal API). Output:

      removed_candidate_rawnode_test.go:60: node 3: StateCandidate, config voters=(1 2)
      removed_candidate_rawnode_test.go:63: PANIC reproduced: runtime error: invalid memory address or nil pointer dereference

- A snapshot restored while the application is still applying the previous `Ready` makes
  the pending `ApplyConfChange` calls apply stale conf changes on top of the snapshot's
  configuration, with no lag involved (`snapshot_during_apply_test.go`):
  [raft-snapshot-during-apply-stale-confchange](../raft-snapshot-during-apply-stale-confchange.md).
- Auto-leave is delayed under the lag (above).
