# etcd-io/raft#234: possible split brain caused by async storage writes?

<https://github.com/etcd-io/raft/issues/234>. Closed 2024-11-28 by the reporter after the
maintainer's (joshuazh-x) explanation. No fix, no PR.

**The report.** A cluster of `{1,2,3}` changes to `{1,2,3,4,5}` (EnterJoint, then LeaveJoint).
Node 1 has received and committed every entry, but its apply thread has stalled
(`AsyncStorageWrites`), so node 1 is still on `{1,2,3}`. A partition then separates `{1,2}` from
`{3,4,5}`. Node 1 wins with `{1,2}` (a majority of `{1,2,3}`) while `{3,4,5}` elect another
leader in the same term. The thread settles it in two steps:

1. Node 1 cannot campaign with a committed but unapplied conf entry (`hup` →
   `hasUnappliedConfChanges`, `raft.go:983,995` at the raft pin `509271dac`).
2. Follow-up: what if node 1 holds the entries but its commit index is below the EnterJoint
   entry `x`? The maintainer's answer: the leader appends LeaveJoint `y` only after applying
   `x`, so every `MsgApp` that carries `y` has `Commit ≥ x`, and the follower's commit index
   becomes `min(Commit, lastnewi) ≥ x`.

## Classification

**N** (not a bug; the maintainer's argument is right), with secondary **A-pre** (the proved
results are for synchronous storage writes only). The maintainer's two steps are exactly the
proof's I2 (the campaign guard) and I1 ("at most one conf entry above `commit`", for every node
and every `MsgApp` slice, given `AppCommitEq`). Under them the dynamic model proves election
safety (`raft_dyn_election_safety`, `Proof/go_etcd_io/raft/v3/Protocol/ResultsDyn.lean:130`),
and the `RawNode` specs follow it in the dynamic mode. That holds only with
`AsyncStorageWrites = false`, a premise of `NewRawNode`, `StartNode` and `RestartNode`
(`Spec/go_etcd_io/raft/v3/NewRawNode.lean:114`, `StartNode.lean:80`, `RestartNode.lean:61`). The
reporter's setting is outside the proof's scope, though not refuted by it.

## The code path and its verification state

Source: the spec, proof and `Link.lean` files directly (no `verified.txt`).

| Go function | State | Spec |
|---|---|---|
| `raft.hup`, `raft.hasUnappliedConfChanges` | verified | `Spec/go_etcd_io/raft/v3/raft__hup.lean:44` (`HupGuard`: no `IsConfEnt` in `unappliedEnts`), `raft__hasUnappliedConfChanges.lean:43` |
| `raft.handleAppendEntries`, `raftLog.maybeAppend` (commit = `min(m.Commit, lastnewi)`) | verified | `Spec/go_etcd_io/raft/v3/raft__handleAppendEntries.lean`, `raftLog__maybeAppend.lean` |
| `raft.sendAppend` (`Commit: r.raftLog.committed`) | verified | `Spec/go_etcd_io/raft/v3/raft__sendAppend.lean`; the model's `AppCommitEq` |
| `stepLeader` `MsgProp` (`alreadyPending`, `raft.go:1326`) | verified | `Spec/go_etcd_io/raft/v3/stepLeader.lean`; model `StepR.propose`/`propConf` |
| `RawNode.Advance` (A1), `RawNode.ApplyConfChange` | verified (dynamic mode) | `Spec/go_etcd_io/raft/v3/RawNode__Advance.lean:78-86`, `RawNode__ApplyConfChange.lean` |
| the asynchronous-writes path (`MsgStorageAppend`/`MsgStorageApply` handed to the application, `RawNode` with `asyncStorageWrites = true`) | outside the specs' scope (`ownRawNode` fixes `asyncStorageWrites' = false`, `InvRawnodeC.lean:53`) | — |

## The argument

1. **Stalled apply, commit known.** `StepR.campaign` (`Protocol/StepR.lean:135-139`) needs
   `NoConfIn r.full applied commit`. With `x` (and `y`) committed and not applied, node 1
   cannot campaign. The code-level spec's `HupGuard` (`Proof/go_etcd_io/raft/v3/SpecResults.lean:68-74`)
   says the same: `hup` either does nothing or campaigns with no conf entry unapplied.
2. **Commit not known (the follow-up).** I1 (`notes/reconfiguration-safety.md` §3;
   `ConfI1`, `Protocol/StepRInv.lean`): of two conf entries of a node's log or of a `MsgApp`'s
   slice, the first is at or below the commit index. If node 1 holds `y`, it got `y` from a
   message whose commit index is at least `x`, and `maybeAppend` sets commit `≥ x`, so case
   1 applies. If node 1 holds only `x`, its configuration is one change behind, and adjacent
   configurations overlap (`enterJointM_overlap`, `Protocol/CfgOverlap.lean:173`). This is
   more general than the maintainer's argument, which considers only the leader that
   appended `y`. I1 covers any sender, a later leader included.
3. **Async writes.** The documented async loop (`doc.go:240-256`) calls `ApplyConfChange` on
   the apply thread before `send(m.GetResponses())`. The `MsgStorageApplyResp` that moves
   `applied` therefore comes after the configuration switch, which is A1 in its async form.
   For an application that follows the documentation, the argument above carries over
   unchanged. The proof does not cover it, because no spec is stated with
   `asyncStorageWrites = true`. An application that sends the apply responses before
   `ApplyConfChange` breaks A1, and the result is the split brain of
   `issues/raft-advance-before-applyconfchange.md`. That is a different trigger from the one
   reported here.

## Proposal

`raft-async-storage-writes`: specify the `RawNode`/`node` API with `AsyncStorageWrites = true`.
`Ready` hands out `MsgStorageAppend`/`MsgStorageApply` with their response lists (the helpers
`needStorageAppendRespMsg`, `newStorageAppendRespMsg` and `newStorageApplyRespMsg` are already
verified). Responses are stepped back as ordinary messages, and A1 becomes the premise "a
`MsgStorageApplyResp` is stepped only after `ApplyConfChange` of every conf entry it covers"
(`GMode.Pre` already has its synchronous form at `MsgStorageApplyResp`,
`StepGhostMode.lean:57-63`). The result is `raft_dyn_election_safety` and
`raft_dyn_committed_agree` reached from an async `RawNode`. Cost: medium. The `raft.Step`
layer is unchanged (it already handles the storage messages). `ownRawNode`'s `Ready`/`Advance`
bookkeeping (`InvRawnode*.lean`) is rewritten for out-of-order append and apply threads.
etcd's server does not use async writes, so this matters for raft's other users.

## Files

None written. `issues/raft-advance-before-applyconfchange.md` and
`issues/raft-track-confchange-application.md` already link etcd-io/raft#234.
