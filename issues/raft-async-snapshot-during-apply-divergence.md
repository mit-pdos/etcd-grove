---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/raft#8 pr merged: added AsyncStorageWrites; its review (and etcd-io/etcd#14627's, where it started) does not discuss a snapshot handed out while committed entries are being applied
candidate: issues/upstream/raft-async-snapshot-during-apply-divergence/
---

# raft: with `AsyncStorageWrites`, a snapshot is handed out while earlier committed entries are being applied, and the documented thread model lets the application apply those entries on top of it

- **Status**: a bug in raft's `AsyncStorageWrites` interface, or at least an unstated precondition. Upstream candidate (2026-10-23, split off
  `raft-snapshot-during-apply-stale-confchange`'s): `issues/upstream/raft-async-snapshot-during-apply-divergence/`,
  branch `fix/raft-async-snapshot-during-apply-divergence` (the hold, `storageAppendHeld`, with
  `TestRawNodeAsyncSnapshotDuringApply`), whose `rawnode.go` change is identical to that candidate's. Reproduced
  by a Go test (public `RawNode` API, one internal read for the log line) at the pin and at etcd-io/raft `main`
  1931ff5. etcd does not enable `AsyncStorageWrites` (no use in etcd's sources), so etcd is not affected; other
  users not checked.
- **Where** (the pinned raft, `.lake/go-src/raft`, fork commit `c8217eb9`):
  - `raft.go:153-187` (`Config.AsyncStorageWrites`): `MsgStorageAppend` (to the append thread) carries
    "snapshots to apply", the writes being to "local storage (raft log and state machine)"; `MsgStorageApply`
    (to the apply thread) carries committed entries; "Messages to different targets can be processed in any
    order."
  - `doc.go:227-258`: the example's append thread only saves the snapshot to storage
    (`saveToStorage(m.State, m.GetEntries(), m.GetSnapshot())`); nothing in the example installs it in the
    state machine.
  - `raft.go:1838`, `1852` (`handleSnapshot`, `restore`): a snapshot past the commit index is restored whether
    or not committed entries handed out earlier (`raftLog.applying > applied`) are still being applied.
    `rawnode.go:155` and `223` then hand it out in the next `MsgStorageAppend`; only new committed entries
    are held back while a snapshot is pending (`log.go:248-258`: "Doing so raises questions about what should
    be applied first"), not those already handed out.
  - raft's own async harness does not cover it: `rafttest`'s append thread (`processAppend`,
    `rafttest/interaction_env_handler_process_append_thread.go:84`) writes the snapshot to `Storage` only,
    and its state machine (`n.History`) is updated only by the apply thread.
- **What happens**: follower 2 gets entry 1 (`"a"`) committed; raft hands it out in a `MsgStorageApply`. Before
  the apply thread has applied it, the leader's snapshot at index 2 (state `"ab"`) arrives; raft restores it
  and hands it out in a `MsgStorageAppend`. The append thread installs it (state `"ab"`) and responds, so raft's
  applied index is 2; then the apply thread applies entry 1 on top: state `"aba"`, which is no prefix's of the
  log. The other order (apply thread first) gives `"ab"`. In a real application the two threads race.
  Reproduction (`raft-async-snapshot-during-apply-divergence/async_snapshot_during_apply_test.go`; it passes
  when the divergence is reproduced):

      cp issues/raft-async-snapshot-during-apply-divergence/async_snapshot_during_apply_test.go <etcd-raft checkout>/
      cd <etcd-raft checkout> && go test -count=1 -run TestAsyncSnapshotDuringApplyDivergence -v .
      ...
      async_snapshot_during_apply_test.go:114: raft handed out the snapshot with applying=1 > applied=0
      async_snapshot_during_apply_test.go:121: state machine "aba", raft applied 2; the log's state at index 2 is "ab"
      --- PASS: TestAsyncSnapshotDuringApplyDivergence

  Run 2026-10-21 (go1.26.9) at the pin, at upstream `main` 1931ff5, and with b556234 (a fix of
  `raft-snapshot-during-apply-stale-confchange` that keeps the pre-snapshot configuration), which does not change it. An application that
  instead follows `doc.go`'s example literally never installs the snapshot's state at all, and applies the
  entries after it on top of a state missing those up to its index.
- **Expected**: either raft does not hand out a snapshot while committed entries handed out earlier are
  unacknowledged, or the documentation says that the application must install a snapshot only after its
  apply thread has applied every `MsgStorageApply` handed out before it (which "processed in any order"
  contradicts), and the example shows where the state machine takes the snapshot.
- **How the proof handles it**: out of scope: the raft proof requires `asyncStorageWrites = false`
  (`Proof/go_etcd_io/raft/v3/InvRawnodeC.lean:53`, `InvBoot.lean:62`).
- **Possible fixes**: (1) hold the snapshot back in `Ready` while `applying > applied`, as
  `hasNextCommittedEnts` already holds back entries while a snapshot is pending; with it everything else bound for
  the append thread (the entries after the snapshot, a `HardState` whose commit index is the snapshot's, and
  `msgsAfterAppend`, whose `MsgAppResp` acknowledges the snapshot), only in this case. With synchronous storage
  this changes nothing (the snapshot's `Ready` already comes after the earlier `Advance`). Implemented
  (`storageAppendHeld` in `rawnode.go`, 2026-10-21) as part of the candidate fix of
  `raft-snapshot-during-apply-stale-confchange`, which needs it; with it this file's test no longer sees the
  snapshot handed out while entry 1 is being applied, and a variant asserting the state machine ends with "ab"
  passes (`issues/upstream/raft-snapshot-during-apply-stale-confchange/meta.md`, "Verification"). (2) Document the ordering
  requirement and fix the example. (3) Send the snapshot to the apply thread as well, ordered with the
  entries: an interface change. Fix (1) does not by itself fix `raft-snapshot-during-apply-stale-confchange`
  (raft's configuration still switches at `restore`), but it makes `appliedSnap` come after the earlier
  entries' acknowledgement, which that issue's "switch the configuration at `appliedSnap`" alternative needs.
- **Found**: 2026-10-21, while working out whether moving the configuration switch of
  `raft-snapshot-during-apply-stale-confchange` to `appliedSnap` fixes it with `AsyncStorageWrites`.
