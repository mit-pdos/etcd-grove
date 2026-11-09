# Requirements on `go.etcd.io/raft/v3` (the raft core, R2; the log, R3)

## from R1

Batch R1 (the node API: `Spec/go_etcd_io/raft/v3/{Model,Api}.lean` and the `node`, `RawNode`,
`MemoryStorage` specs) proves its specs over the raft struct and its log. What its sketches need,
in plain terms. Cite the R1 vocabulary by name; state your own predicates over the R1 models
(`LogEntry`, `HardState`, `Snapshot`, `Msg`, `Membership`, `StorState`, `Durable`, `Batch`).

1. **One token for the raft struct** (R2: `raft`, with R3's `raftLog`/`unstable`/`readOnly` and
   R4's tracker inside), held by `rawNode rn γ id` (`Api.lean`). Its specs are what `RawNode`'s
   methods call: `newRaft`, `raft.Step`, `raft.tick`, `raft.applyConfChange`, `raft.softState`,
   `raft.hardState`, `raft.hasLeader`, and the getters `getStatus`, `getBasicStatus`,
   `getProgressCopy` (`status.go`: **R1 left these to R2**, since they are stated over the raft
   struct), and `needStorageAppendMsg`, `needStorageAppendRespMsg`, `newStorageAppendMsg`,
   `newStorageAppendRespMsg`, `newStorageApplyMsg`, `newStorageApplyRespMsg`,
   `RawNode.readyWithoutAccept`, `RawNode.acceptReady`, `RawNode.applyUnstableEntries`
   (`rawnode.go`, internal; left out by R1 for the same reason).
   ```go
   r := newRaft(config)                       // NewRawNode
   _ = rn.raft.Step(m)                        // Step, Propose, Campaign, ReadIndex, Advance
   cs := rn.raft.applyConfChange(cc.AsV2())   // ApplyConfChange
   ```
   Used by: `NewRawNode.spec`, every `RawNode__*.spec`, `node__run.spec`.

2. **`newRaft(c)`**: with `ConfigOk c` (`Api.lean`: `validate` passes, size limits not both 0,
   `ReadOnlySafe`, sync storage writes, conf-change validation on), a storage contract
   `isStorage c.Storage S cf` and `S σ`, the restart premises of `RestartNode.spec` (`Applied` in
   `{0} ∪ [σ.off, σ.hs.commit]`; the configuration `cf σ` is `confAt γ a m` for an `a` in
   `[max σ.off Applied, σ.hs.commit]`), and the client's update over `raftState γ id D` checking
   `StorageHolds D σ`: no panic (the `ConfState` round-trip check passes for a valid configuration:
   `nonissues/raft-restore-malformed-confstate-panic.md`), the update fired at the `InitialState`
   read, and the raft token at: term/vote from `σ.hs`, committed `σ.hs.commit`, applied
   `max σ.off Applied`, the log = `σ`'s stable entries, the tracker at `m`, follower.
   Used by: `NewRawNode.spec`, `RestartNode.spec`, `StartNode.spec`.

3. **`raft.Step(m)` for each message source**, keeping the cluster invariants behind the R1
   vocabulary: a received message with `msgSent γ m`, `msgCredit γ m`, `m.to = id`; a local
   proposal with the client's update (`node.Propose.spec`'s `□?γ.dup AU`); a local read with its
   `readCtx`; the local reports (`MsgUnreachable`, `MsgSnapStatus`, `MsgTransferLeader`,
   `MsgHup`, `MsgForgetLeader`) with nothing. Errors: only `ErrProposalDropped`, for a `MsgProp`
   (`RawNode.Step.spec`, `RawNode.Propose.spec`). The leader's commit fires the deposited proposal
   updates (`committedOps` grows by `opsOf` of the committed entry); a `ReadOnlySafe` read
   confirmed by a quorum fires the read update at the commit index and records `readState`.
   Every message raft queues gets its `msgSent` when the batch's enter update fires (or the check
   update, at a leader), and its `msgCredit` at once.
   Used by: `node.Step.spec`, `node.Propose.spec`, `node.ReadIndex.spec`, `readyGot`.

4. **The batch facts** (`Model.lean`'s `BatchOk`): what `readyWithoutAccept` reads from the log
   (R3: `nextUnstableEnts`, `nextCommittedEnts(true)`, `nextUnstableSnapshot`,
   `hasNextUnstableSnapshot`): committed entries follow the delivered ones; with a snapshot, none;
   the new commit covers the committed entries and lies within the durable log after the batch;
   the unstable entries start after the old commit; `MustSync` as computed. And: entries `≤`
   applied are in the storage (raft never asks the storage for an unapplied entry it compacted:
   `issues/etcd-compact-past-raft-applied.md`), which is how `stor_compact.spec`'s `appliedLb`
   suffices.
   Used by: `readyGot` (`RawNode.Ready.spec`, `readyChan_recv.spec`).

5. **`raft.applyConfChange(cc)`** at a tracker holding `m` with `Membership.applyChange c m =
   some m'`: no panic, the tracker at `m'`, the returned `ConfState` lists `m'`; a snapshot's
   configuration switched at `Advance` (`appliedSnap`, the fork's a2 fix).
   Used by: `node.ApplyConfChange.spec`, `RawNode.ApplyConfChange.spec`, `node.Advance.spec`.

6. **Loggers**: raft calls its `Logger` only through `loggerOk`'s methods outside a failure path;
   `SetLogger`/`getLogger` (`logger.go`, R2) keep a logger meeting `loggerOk` (etcd calls
   `raft.SetLogger` at `newRaftNode`; `MemoryStorage`'s panics go through `getLogger`).
   Used by: every R1 spec taking `loggerOk`.

7. **util.go's helpers** `isMsgInArray`, `voteRespMsgType`, `entsSize`, `limitSize`,
   `payloadSize`, `payloadsSize`, `extend`, `assertConfStatesEquivalent`, `Describe*`, and
   `types.go`'s `pbEntryID`: used by the log and the raft core, not by R1's statements; R1 left them
   to R3 (util.go is listed in both batches). R1 needs only: `limitSize` returns a non-empty prefix
   of a non-empty list (`MemoryStorage.Entries.spec`).
