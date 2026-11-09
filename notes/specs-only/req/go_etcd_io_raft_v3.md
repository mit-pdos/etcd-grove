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
   `{0} ∪ [σ.off, σ.hs.commit]`; the configuration `cf σ` is `confAt γ a m` for a committed point
   `a ≥ max σ.off Applied`, not bounded by the stored commit: item 8; the stored snapshot empty or
   `snapValid`), and the client's update over `raftState γ id D` checking
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

### from R1, round 1

8. **A configuration ahead of the log.** `RestartNode.spec`/`NewRawNode.spec` now take the
   configuration at any committed point `a ≥ max σ.off Applied` (no longer `a ≤ σ.hs.commit`:
   etcd restarts at the backend's configuration, at a consistent index a crash can leave above the
   WAL's commit), and a snapshot may carry the configuration at a committed point at or after its
   index (`snap_make.spec`; etcd's replay snapshots,
   `nonissues/etcd-replay-snapshot-confstate-ahead.md`), which a node installing it takes at
   `Advance`. R2's invariant must carry a tracker at a committed configuration ahead of the node's
   commit index. If it cannot, say so: R1 reverts to `a ≤ commit` as a filed scope restriction.
   **The safety argument to carry** (R1's round-2 reviewer, `reviews/R1-round2.md`): the old paper
   proof (`specs-ref/notes/reconfiguration-safety.md`) assumes `applied ≤ a ≤ commit` (Cfg), the
   campaign configuration a fold of the candidate's own log (I2), witnesses up to the commit only
   (`W(n)`), and in section 7's far case that the candidate's configuration's conf entries are all
   `≤ k_c`; a configuration ahead breaks all four. What closes it: *a node cannot win before it holds
   the committed prefix through its configuration's last conf entry `p`*. (1) Some commit fact covers
   `p`; by its "at most one conf entry above its configuration index", its quorum's configuration is
   adjacent to `C_a`, so its quorum meets every candidate quorum. (2) If the campaign term `T` is at
   most that fact's term, the overlapping voter has a durable term at least as high (acks are sent
   after persistence, `msgsAfterAppend`) or a newer last log term, and refuses. (3) Otherwise
   adjacent-case leader completeness puts the entry in the candidate's log. After that the
   candidate's configuration is the fold of its own log, and the old cases apply with `a` in place
   of `k_c` and global witnesses for the positions in `(commit, a]`. (Unchecked: whether it closes
   with no further repair.) Also, `node.Advance.spec`/`RawNode.Advance.spec` (round 2) let the client
   name the view's point after a snapshot (any committed `a ≥ s.index` with `confAt γ a m`,
   `s.conf.Is m`): `ackPost`'s snapshot arm should give the same wand rather than `∃ a`.
9. **The stored snapshot** is empty or `snapValid` at a start (premise of `RestartNode`), and stays
   so (`stor_read.spec`'s guarantee), so that `maybeSendSnapshot` sends only valid snapshots
   (`msgSent_snap.spec`).
10. **`msgSent_replaceSnap.spec`** now requires the new snapshot to be a prefix of the sender's
    delivered log (`isNode n γ m.src ∗ deliveredLb n γ l`) and (round 2) its term at most the
    message's (`s'.term ≤ m.term`; `issues/etcd-merged-snapshot-stale-term.md`, the fork's guard):
    R2's invariant must make a leader's `MsgAppResp` accounting sound for a follower restoring such
    a snapshot. (For 2d: etcd meets the term premise through `m.GetTerm() == apply.raftTerm` and the
    fact that applied entries' terms are at most the node's current term.)
11. **(Round 2, R2's request) the `RawNode` phases.** R1's `RawNode` specs now use R2's
    `rawNodeAt rn γ id k adv` (`NewRawNode` gives `... 0 false`; every method keeps it; `Ready` takes
    `... k false` and gives `... (k+1) true`; `Advance` gives `... k false`; `HasReady` with a
    `readyKept rn k rd` gives `readyFresh ... rd` on `false`). R2 owns these predicates.

## from R3

Batch R3 (the log, `Spec/go_etcd_io/raft/v3/ApiLog.lean`) reads the storage through R1's
`isStorage st S cf` and states the client's storage writes as its own laws (`logStor_*`), from
which R1's `readyStor_*`, `stor_*` are meant to be realized. What R3 needs of R1:

1. **`Entries`' slice has no spare capacity** (or the caller owns it). `raftLog.slice` appends the
   unstable part to the storage's slice with `extend`, which writes into `dst`'s capacity when it
   suffices; with only `entriesRO` of the returned slice that write is unjustified (and a `Storage`
   handing out a slice with capacity into its own array would be corrupted). `MemoryStorage.Entries`
   returns `ents[:len(ents):len(ents)]`. Please add `⌜sl.len = sl.cap⌝` (or `ownSliceCap`) to
   `isStorage`'s `Entries` success case.
   ```go
   ents, err := l.storage.Entries(lo, cut, uint64(maxSize)) // log.go: slice
   ...
   return extend(ents, unstable), nil
   ```
   Used by: `raftLog.slice.spec` (and `entries`, `nextCommittedEnts`, `scan`).
2. **The mapping R3 intends** (for R1's realization of its node predicates; nothing to change):
   `nodeStorage n γ S` ~ `logStorage l S (snapValid γ) N` (the log's invariant, `N` disjoint from
   the client's); `readyStor n so k es` ~ `logPending l h snapLeft entsLeft` (`acceptUnstable`'s
   batch `h = ls.handout`); `storSnapLb n j` ~ `logSnapLb l j`; `appliedLb n i` ~ `∃ t, logFloor l i
   t` (with R2's committed-prefix facts for `stor_createSnapshot`'s term); `stor_read` ~
   `logStor_read`. The storage writes' outer mask `⊤` (R1's round 1) is an instance of R3's
   `∀ Eo ⊇ ↑N`. `Advance` must absorb the written batch (`raftLog_absorb`) before the next
   `acceptReady` (`raftLog.acceptUnstable.spec` takes `ls.handing = false`).
3. **`InitialState` while starting**: `newRaft` calls it right after `newLogWithSize`, which keeps
   `S σ` inside `raftLog` (starting mode); `raftLog_borrowStarting` lends it out for the call.
   R1's non-atomic `InitialState` contract is fine as is.

## from R2

Batch R2 (the raft core: `Spec/go_etcd_io/raft/v3/ApiCore.lean` and the `raft__*`, `step*`,
`newRaft`, `getStatus`, `RawNode__readyWithoutAccept`/`acceptReady` specs). Report:
`notes/specs-only/batch-R2.md`.

### To R1 (the node API)

1. **`RawNode.Ready.spec` is false as stated** (a hard-rule finding): its pre is `rawNode ∗ nodeDriver
   rn γ st`, and the batch's `readyEnter` gives the driver back before `Advance`; a second
   `RawNode.Ready` then panics in `acceptReady` ("two accepted Ready structs without call to
   Advance") whenever the first batch queued acknowledgements (committed entries, entries, a
   snapshot, a self-vote). Fix: take R2's `rawNodeAt rn γ id k false` (no acknowledgement queued;
   `rawNode_at.spec`), give back `rawNodeAt rn γ id (k+1) true`; `RawNode.Advance` takes `rawNodeAt
   ... true` (or any) and gives `... false`. Snippet `examples/specreq/raftcore/ready.go`
   (`ReqReadyAdvance`). `node.Ready` is fine (`run` waits on `advancec`).
2. **`RawNode.HasReady.spec`** should give back freshness: with `rawNodeAt rn γ id k adv ∗ readyKept
   rn k rd`, a `false` result gives `readyFresh rn γ id k adv rd`. `node.run` sends a `Ready`
   computed before other steps when `HasReady()` is then false (`ReqReadyStale`); R2's
   `ready_handout` needs a fresh `Ready`.
3. **Building the `RawNode`**: `NewRawNode`'s proof is `newRaft.spec`, the allocation, `softState`,
   `hardState`, then `raftBoot_bind.spec` (which gives `rawNodeAt rn γ id 0 false` and R1's node
   predicates keyed by `rn`). Calls into the raft struct open `rawNodeAt` with `rawNodeAt_core.spec`;
   `Advance`'s loop uses `rawNodeAt_advance.spec` and `raft.Step` with `StepSrc.ack`.
4. **R1's predicates keyed by `rn` appear in R2's statements** (`ackPre`/`ackPost`,
   `raft.applyConfChange`, `raftBoot_bind`, `ready_handout`), next to `raftOf rn r`. Their
   realization must reach the raft struct's ghost state from `rn` (`rn.raft ↦□ r`, and names
   attached to `r`).
5. **The term bound.** `raft.Step`/`tick*` take no term budget: each campaign takes a time receipt
   from raft's own Go steps, and the cluster invariant bounds every term (and index) by the
   receipts. The fact that the execution's step bound is below `2^64 - 1` must enter at
   `cluster_alloc.spec` (the owner of the bound, `notes/bounds-plan.md`): R1's statement has no
   such premise today. Open question for the user (`batch-R2.md`).
6. `node.go`'s and `rawnode.go`'s calls `rn.raft.applyConfChange(cc.AsV2())`: R2's spec takes the
   `*ConfChangeV2` and the client's `c` with `∀ mm, applyChange (.v2 c2) mm = applyChange c mm`
   (3h's `AsV2` law).

### To R3 (the log, `readOnly`)

What `raftCore`'s realization and the proof sketches of `raft.Step`, `handle*`, `restore`,
`maybeSendAppend`, `hasUnappliedConfChanges`, `readyWithoutAccept`/`acceptReady` use:
- `raftLog` over a `Storage` meeting R1's `isStorage` with contents `S σ` held in an invariant
  (atomic reads): `term`, `entries`, `slice`/`scan` within `[firstIndex - 1, lastIndex]` (no panic:
  the compaction point at most the applied index), `snapshot` (unstable's, else the storage's);
  `lastEntryID`, `isUpToDate`, `matchTerm`, `findConflictByTerm`, `zeroTermOnOutOfBounds`;
- `maybeAppend(a, commit)` panics only on a conflict at or below `committed` (R2 rules it out by
  log matching from `msgSent`): state that precondition, and `commitTo(i)`'s (`i ≤ lastIndex`);
- `append` (the leader's own), `restore(s)` (the log becomes the snapshot, committed at its index,
  pending), `stableTo(id)` (only if the id's term matches, R2 steps it after the storage write),
  `stableSnapTo`, `appliedTo(i, size)` (`applied ≤ i ≤ committed`: R2 passes at most the delivered
  index), `acceptUnstable`, `acceptApplying(i, size, true)`;
- `nextUnstableEnts`, `nextCommittedEnts(true)`, `hasNextUnstableEnts`, `hasNextCommittedEnts`,
  `hasNextUnstableSnapshot`/`nextUnstableSnapshot`, `hasNextOrInProgressSnapshot`,
  `hasNextOrInProgressUnstableEnts`: as pure functions of an abstract log state that R2 can relate
  to R1's `BatchOk` (committed entries follow the applying index; the unstable entries start after
  the in-progress offset), and **monotone between `acceptUnstable`/`acceptApplying`** (no step
  empties a non-empty "next" set without making another one non-empty: `ReqReadyStale`'s argument);
- `readOnly`: `addRequest(index, m)` keeps the request message (one entry, the context),
  `recvAck`, `maybeAdvance(voters)` returns the requests acknowledged by a quorum of `voters`
  (R4's `quorum.JointConfig`), in order, with the index they were registered at; `heartbeatCtx`
  the last pending request's context (or empty).
- util.go: `voteRespMsgType` of the four vote types, `entsSize`, `payloadsSize`,
  `assertConfStatesEquivalent` (no panic when the `ConfState` lists the tracker's configuration).
