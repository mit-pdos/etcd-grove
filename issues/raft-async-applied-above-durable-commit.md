---
upstream: unchecked
checked: 2026-10-16
links:
  - etcd-io/raft#37 pr open: related, makes it wider: with `AsyncStorageWritesNonLocalQuorum` the applied index can also pass the node's durable last index (`notes/pr-verify/raft-37.md`)
---

# raft: with `AsyncStorageWrites`, the state machine can apply past the durable commit index, and restarting with that `Config.Applied` panics

- **Status**: unstated precondition (documentation). Found while verifying etcd-io/raft#37; the
  behavior is in the pinned code, without the PR.
- **Where** (raft v3.7 fork, `509271dac`):
  - `doc.go:189-194`: with asynchronous storage writes, append-thread messages (entries and the
    `HardState`) and apply-thread messages (committed entries) "can be processed in any order".
  - `raft.go:147-150` (`Config.Applied`): "the last applied index. It should only be set when
    restarting raft. raft will not return entries to the application smaller or equal to
    Applied."
  - `raft.go:484-485` (`newRaft`): `raftlog.appliedTo(c.Applied, 0)`; `log.go:332-334`
    (`raftLog.appliedTo`) panics if `Applied` is above the commit index the storage's
    `HardState` restored.
- **What happens**: the `MsgStorageAppend` that persists `HardState.Commit = 12` and the
  `MsgStorageApply` that hands entry 12 to the state machine go to different threads. If the
  apply thread finishes first and the node crashes before the append thread writes the
  `HardState`, the state machine's applied index (12) is above the durable commit (11). An
  application that restarts with `Config.Applied` = its state machine's applied index, as the
  field's documentation suggests, panics in `NewRawNode`: "applied(12) is out of range
  [prevApplied(10), committed(11)]". Reproduction:
  `issues/raft-async-applied-above-durable-commit/rawnode_async_restart_applied_test.go`
  (`cp` it into the fork at `509271dac`, `go test -run
  TestAsyncStorageWritesRestartAppliedAboveDurableCommit .`; it passes, showing the panic).
- **Expected**: either the documentation states the precondition (`Config.Applied` must not
  exceed the durable `HardState.Commit`, so an asynchronous application has to order its
  `HardState` write before recording an applied index past it, or clamp `Applied` on restart),
  or `newRaft` accepts an `Applied` above the restored commit (raising `committed` to it is
  safe when the entries are durable locally: they were committed when handed out).
- **How the proof handles it**: out of scope. Every `RawNode` invariant has
  `rnv.asyncStorageWrites' = false` (`Proof/go_etcd_io/raft/v3/InvRawnode.lean`, `"%Hasync"`),
  and `NewRawNode.spec` requires `cv.AsyncStorageWrites' = false` and `cv.Applied' = W64 0`
  (`Spec/go_etcd_io/raft/v3/NewRawNode.lean`).
- **Possible fixes**: document the ordering requirement on `Config.Applied` and in `doc.go`'s
  asynchronous-writes section; or let `newRaft` move `committed` up to `Applied` when
  `Applied <= lastIndex`.
- **Found**: 2026-10-16, by the reviewer of the raft#37 verification
  (`notes/pr-verify/raft-37.md`).
