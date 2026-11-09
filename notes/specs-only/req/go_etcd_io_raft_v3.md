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

### from R3, round 1

4. **To R2: the index bound as `lastIndex < 2^63`.** R3's specs keep their bounds local:
   `slice`/`entries`/`scan` take `hi - lo < 2^63` (`extend`'s `int` sum), `nextCommittedEnts` the
   same unless paused or a snapshot is pending; `append` `k + |es| < 2^64`, `maybeAppend`
   `prev + |es| < 2^64`, `restore` `s.index + 1 < 2^64`. If R2's step-receipt bound on terms and
   indices (its item 5 to R1) is stated as **every index below `2^63`** (not `2^64 - 1`), one fact
   discharges all of them (every range of indices is then below `2^63`).
   Used by: `raft.maybeSendAppend`, `hasUnappliedConfChanges`, `readyWithoutAccept`, `appendEntry`,
   `handleAppendEntries`, `restore`.
5. **To R1, R2 and 3h: a `MsgApp`'s entries as an indexed slice.** `raftLog.maybeAppend.spec` needs
   `entriesRO a.entries' (prev + 1) es` (Go reads each entry's `Index`: `findConflict`'s
   `pbEntryID`, `append`'s `ents[0].GetIndex()`, `acceptInProgress`'s last index) and the slice
   with no spare capacity (`⌜len = cap⌝` or its `ownSliceCap`: `unstable` may adopt it and append
   into it later). That is the weakest the code needs. Sources: R1's `Msg` should index its entries
   (their first index, `m.index + 1` for a `MsgApp`), `msgSent γ m` of a `MsgApp` state it; 3h's
   `msgPts` expose `entriesRO entsSlice (m.index + 1) m.entries` with the capacity (a decoded
   message's slice is exactly allocated); R2's `logSliceFromMsgApp.spec` name `a.entries'` as that
   slice. Same for `MsgStorageApplyResp`'s entries (`entsSize`, `payloadsSize`, the last
   `GetIndex()`), and `appendEntry`'s `cloned` (`make(len, len)`: R2's own).
   ```go
   a := logSliceFromMsgApp(m)                                   // raft.go:1809
   if mlastIndex, ok := r.raftLog.maybeAppend(a, m.GetCommit()); ok { ... }
   ```
6. **To R1: the storage read law and floors** (round 1, provability F6, completeness F5):
   `logStor_read` now takes `logSnapLb l j`, gives `j ≤ σ.snap.index` and commits `logSnapLb l
   σ.snap.index`, as `stor_read`; `logFloor_agree` lets R2 tie a floor's term to the committed log.
   `raftLog_publish` now publishes from frozen terms (written committed entries), so an applied index
   is a floor after a truncation or a restore between `Ready` and `Advance`; `logStor_install`'s
   COMM gives a floor at the snapshot (R1's `readyStor_install` may keep it for the acknowledgement).

## from R4

Batch R4 (tracker, quorum, confchange: `Spec/go_etcd_io/raft/v3/{tracker,quorum,confchange}/`,
namespaces `Tracker`, `Quorum`, `ConfChange`; report `notes/specs-only/batch-R4.md`).

### To R1 (the node API's model and laws)

1. **Integration of the configuration model.** R4's `tracker/Model.lean` defines `Tracker.Membership`
   with R1's five fields and helpers (`simple`, `empty`, `ids`, `isJoint`) and `Membership.Valid`
   (transparent), and imports nothing of raft's, so that R1's `Model.lean` can import it. Replace
   R1's `structure Membership` (and its helpers) by `abbrev Membership := Tracker.Membership`, the
   opaque `Membership.Valid` by `Tracker.Membership.Valid`, and the opaque `Membership.applyChange`
   by (`confchange/Model.lean`):
   ```lean
   def Membership.applyChange : ConfChangeI → Membership → Option Membership
     | .v1 cc, m => ConfChange.changeV2 ⟨ConfChange.TransitionAuto, [⟨cc.type, cc.nodeId⟩]⟩ m
     | .v2 c, m => ConfChange.changeV2 ⟨c.transition, c.changes.map (fun s => ⟨s.type, s.nodeId⟩)⟩ m
   ```
   (`AsV2()` of a legacy change: one change, transition `Auto`.) R1's `ConfState.Is cs m` is
   `ConfChange.Lists cs.voters cs.learners cs.votersOutgoing cs.learnersNext cs.autoLeave m`.
2. **R1's law `Membership.applyChange_v1.spec` is false as stated** (two cases): at the empty
   configuration a node-`0` or `UpdateNode` change is the error "removed all voters" (`apply` checks
   the incoming voters after every change list), not `some m`; and a change of an unknown type is
   the error "unexpected conf type", where the law's last branch removes the node. R4's
   `ConfChange.changeV2_single.spec` is the corrected statement (premise `m.voters ≠ ∅`; unknown
   type: `none`); R1's law becomes its instance at `m.voters ≠ ∅` with an unknown-type `none`
   branch. etcd's uses are unaffected (a configuration with voters, the four known types).
3. **`Membership.Valid` has no size bound and no local-target condition.** Valid is what
   `checkInvariants` accepts plus what every reachable configuration has (no id `0`; voters unless
   empty; no staged learner among the incoming voters), exactly what `Restore` round-trips.
   `Membership.simple_valid.spec`'s premises `vs ≠ []`, `isLocalTarget id = false`, `vs.length <
   2^62` are not needed (R4's `ConfChange.simple_valid.spec` takes only `W64 0 ∉ vs`; the empty
   configuration is valid). The `2^62` of Perennial's `slices.Sort` is a premise of the specs that
   sort (`Visit`, `VoterNodes`, `ConfState`, `CommittedIndex`), kept local (PRINCIPLES, "Keep a
   tool's temporary limitation as local as possible"); R2 sources it (below).
4. **`ConfigOk`'s ring capacity.** `NewInflights` (called by confchange for every new peer and by
   raft's `reset`) takes `0 ≤ size ≤ 2^62` (`Tracker.inflightsMax`: below it the ring's `int`
   arithmetic does not wrap; a Go program could not allocate a ring that large, but the model has no
   memory bound). Please add `sint.Z cv.MaxInflightMsgs' ≤ inflightsMax` to `ConfigOk` (a scope
   restriction on an option no client sets near it: etcd 4096, the examples 256), or tell R4 to
   carry it otherwise. Used by: `NewInflights.spec`, `ConfChange.BaseOf` (every `Changer` spec,
   `Restore.spec`).
5. `statusOwn`'s `Config` (from `Config.Clone`) has `AutoLeave` false
   (`issues/raft-config-clone-autoleave.md` in `specs-ref`): `Config.Clone.spec` gives
   `configOwn cfg' (own 1) {m with autoLeave := false}`. `statusOwn_progress` can be stated over
   `Tracker.progressValOwn` (each `Progress` value with its own `Inflights` clone).

### To R2 (the raft core)

1. **The tracker inside `raftCore`** is `Tracker.progressTracker (structFieldRef raft "trk" r) T`
   (`T : Tracker.TrackerV`: configuration, `*Progress` map `T.prs` (R2's `ρ.prs`), progress values
   `T.pv`, votes, ring capacities; transparent: `∃ tv, r.trk ↦ tv ∗ trackerOwn tv T`, with the
   opaque `configOwn`, `inflightsOwn`, and `TrackerOk`: the map tracks exactly the configuration's
   ids, learners marked). `raftCore_peek`'s `ownMap mp _ ρ.prs` is `progressMapOwn`'s map; raft's
   direct reads `r.trk.Voters[0][id]`, `len(r.trk.Voters[1])`, `r.trk.Config.AutoLeave`,
   `r.trk.Voters` (to `maybeAdvance`) go through `Tracker.configOwn_open.spec` (quorum's transparent
   `jointConfigOwn`). Each `*Progress` is `progressOwn pr P` (the struct points-to, transparent;
   raft writes its fields directly).
2. **`Visit`'s footprint is only the `Progress` field and map, at a share** (`dq`), not the tracker:
   its callbacks (`bcastAppend`'s `maybeSendAppend`) read `r.trk.Progress[id]` with another share.
   The callback's triple is indexed by the sorted prefix visited (`Quorum.sorted`).
3. **The sort bound.** `Visit`, `QuorumActive`, `VoterNodes`, `Committed`, `ConfState` take
   `GMap.size … ≤ Quorum.sortMax` (`2^62`) of the sets they sort. Its source on R2's side: the
   number of ids of a committed configuration is at most the bootstrap peers plus the committed
   conf entries, below the step bound R2 already relies on for terms and indices (its open
   question 5: each id a change adds costs the Go steps that decode it), kept in R2's invariant
   over `confAt`. If R2 cannot source it, the alternative is a bound in `Membership.Valid` (R1's
   first design), with `changeV2` refusing a change past it: less local, a margin at every client.
4. **Quorum facts for safety.** `ProgressTracker.Committed.spec`: `Quorum.JointIdx voters
   outgoing (matchOf T.pv) N`, and `Quorum.jointIdx_quorum.spec` (a joint quorum matched `N`).
   `TallyVotes.spec`: the result is `Quorum.jointVote` (won iff `JointQ` of the granted votes).
   Intersection: `Quorum.jointQ_intersect.spec` over `Quorum.Adjacent`, and
   `ConfChange.changeV2_adjacent.spec` (a change moves the voters one step, from a configuration
   with voters, both incoming voter sets below `2^63` in all).
5. **`applyConfChange`/`newRaft`/`appliedSnap`**: `Changer.{Simple,EnterJoint,LeaveJoint}.spec`
   (`changed B (F m)`: no error iff the model's `F m = some m'`; then `configOwn` at `m'` and a fresh
   progress map `Carried` from the tracker's: each peer's `Progress` the old one with its learner mark
   updated, or fresh with `Next = max(LastIndex, 1)` (not `LastIndex + 1`), `Match = 0`, probing,
   recently active), and `Restore.spec` (from `MakeProgressTracker`'s empty tracker, `result B
   (restore …)`; `ConfChange.restore_lists.spec`: a `ConfState` listing a valid `m` restores to
   `m`). `switchToConfig` stores the result in `r.trk.Config`/`r.trk.Progress` (the old map's
   `Progress` structs are not given back: their rings moved to the copies). `ProgressTracker.ConfState`
   gives `confStatePts` of the sorted lists (`assertConfStatesEquivalent`).
6. **`getProgressCopy`'s `progressCopyOwn mp`**: `∃ pm Ps, ownMap mp (own 1) pm ∗ [∗map] _ ↦ p;P ∈
   pm;Ps, Tracker.progressValOwn p P` (each value's `Inflights` from `Inflights.Clone`).
7. `Progress.SentEntries.spec` takes `P.state ≠ .snapshot` (Go panics) and, for entries sent to a
   replicating peer, a ring that is not full (raft sends none then: `raft.go:639`).

### To R3 (the log, `readOnly`)

`jointConfigOwn c dq s0 s1`, `MajorityIdx`, `JointIdx` are now `Quorum.jointConfigOwn`,
`Quorum.MajorityIdx`, `Quorum.JointIdx` (same signatures and bodies: delete the provisional ones
from `ApiLog.lean`). `Quorum.isAckedIndexer l P acked` is the `AckedIndexer` contract
`maybeAdvance`'s sketch needs (`readOnly` with `P = readOnly ro rs`, `acked = (rs.acks !! ·)`,
from `readOnly.AckedIndex.spec`). `JointConfig.CommittedIndex.spec`'s size premise is
`GMap.size s ≤ Quorum.sortMax` for each half (R3's `(elements s).length ≤ 2^62`);
`Quorum.jointIdx_mem.spec` gives the reslice bound.

## from R2 (round 1 repairs)

### To R1

7. **The term and index bound** (provability review 1.3; first tier): `cluster_alloc.spec` should
   carry the execution's step bound, inside the statement (an instance binder, e.g.
   `∀ [ReceiptBoundLe GF (2^63)]`, or a named constant), so that raft's cluster invariant can hold a
   time receipt per term increase and per appended entry (`ApiCore.lean`'s realization item 5).
   `2^63` rather than `2^64 - 2`: R3's log specs take `lastIndex < 2^63` range premises, which the
   same bound then discharges. Without it, `raft.Step` (a campaign at `Term = 2^64 - 1` wraps the
   term, `raft.go:926`, then `send` panics, `:532`), `hup`, the ticks and `stepCandidate` are false.
8. **`RawNode.HasReady.spec`, `false` case**: also give `⌜readyEmpty rd⌝` (`ApiCore.lean`; the
   monotonicity argument is the realization's item 6). `ReqReadyStale` needs it.
9. **`RawNode.Advance.spec`'s proof** is now: `rawNodeAt_advance.spec` (it takes your `Advance` pre
   and its closing gives your post exactly, the snapshot arm with your client-chosen view wand), a
   `raft.Step` with `StepSrc.ack rn` per queued acknowledgement (`ackOk`, never a proposal:
   `ackOk_type`), the closing. `ackPre`/`ackPost` are gone.
10. **`RawNode.Bootstrap.spec`'s proof** is `rawNodeAt_bootstrap.spec` (the window: the struct open at
    the empty log, `prevHardSt`, `committedLb γ boot`), `becomeFollower.spec`, R3's `raftLog` append
    and commit write (through `raftOpen_log`), the closing, then `raft.applyConfChange.spec` per
    peer, which now takes `committedLb γ l` (not `deliveredLb`). It needs each bootstrap entry's
    decision `confDecided γ k (.apply (.v1 AddNode…))`: `cluster_alloc` gives them to the client,
    but `Bootstrap`'s pre does not take them. Please add a law `bootLog_decided.spec : bootLog γ boot
    ∗ ⌜BootLog ps boot⌝ ⊢ [∗list] k, confDecided γ k (...)` (or take them in `Bootstrap`'s pre).
11. **`loggerOk_nonnil.spec`** (a law about your `loggerOk`) is stated in `ApiCore.lean`; move it to
    `Api.lean` if you prefer. `defaultLogger_loggerOk.spec` and `raft_init.spec` give the default
    loggers' contract.
12. `NewRawNode`: `newRaft.spec`'s post now gives `cv' = Config.defaulted cv lg` (so
    `AsyncStorageWrites` read back is `cv`'s); `NewRawNode.spec` could state the same.
13. `node.run`'s reads between computing a `Ready` and sending it: `readyFresh_ro.spec` (a read-only
    share, `raftRO`, which the getters and `raftRO_peek` take).
14. `stepIn`'s received case is up to the sender for a `MsgProp`: `node.run`'s `propc` arm
    (`node.go:388`) rewrites `From` of a proposal `node.Step` received.
15. Not done (second tier): laws for `TickQuiesced` (`electionElapsed++`) and `WithProgress` (R4's
    `Visit` read-only); neither has a user in scope.

## from 2f

Batch 2f (rafthttp, `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Api.lean`, namespace
`Rafthttp`). Report: `notes/specs-only/batch-2f.md`.

1. **R1's question S8 (`reviews/R1-completeness-1.md`): rafthttp delivers each message at most
   once.** Every path dequeues a message once: `peer.send` puts it on one channel without blocking
   (full: dropped); a stream writer encodes it once on its one live connection, and a broken
   connection's queue is dropped with its channel (`closeUnlocked`); the reader decodes each frame
   of its one response once; the pipeline `POST`s it once with no retry, and Go's client never
   replays a `POST` (`Request.isReplayable`); a `GET` it may replay (a stream's dial) opens a second
   handler run whose bytes no client reads. So etcd's one-shot credits (`γ.dup = false`) are sound
   over rafthttp: `Transport.Send.spec` takes `msgCredit γ m` and the receiver's `Process` gets it
   once (`Rafthttp.raftOk`, `recvd`). Nothing to change in R1.
2. **The `MsgApp` shape of a sent message**, as a law of `msgSent` (or a fact of `BatchOk` for the
   `Ready`'s messages): a `MsgApp` of node `id` has `src = id`, `vote = 0`, `snapshot = none`,
   `reject = false`, `rejectHint = 0`, `context = []` (raft's one constructor, `maybeSendAppend`,
   `raft.go:651-658`, sets only `To`, `Type`, `Index`, `LogTerm`, `Entries`, `Commit`; `send` sets
   `From = r.id` and `Term`). The msgappv2 stream's short frame carries only the entries and the
   commit, and the receiver rebuilds the rest (`From` from the dialed peer, the other fields zero):
   without the shape the decoded copy is a different `Msg` and its `msgSent` would not hold.
   ```go
   // msgappv2_codec.go:95 (encoder) / 185-193 (decoder)
   case enc.index == m.GetIndex() && enc.term == m.GetLogTerm() && m.GetLogTerm() == m.GetTerm():
   m = raftpb.Message{Type: MsgApp, From: dec.remote, To: dec.local, Term: dec.term, LogTerm: dec.term, Index: dec.index}
   ```
   Wanted: `msgSent_appShape.spec : msgSent γ m ∗ ⌜m.type = MsgApp⌝ ⊢ ⌜m.vote = 0 ∧ m.snapshot =
   none ∧ m.reject = false ∧ m.rejectHint = 0 ∧ m.context = []⌝`, and that a `Ready` of node `id`
   (`readyGot`) hands out messages with `m.src = id` (a `BatchOk` conjunct, or a law of
   `msgSent` with `isNode`). Used by: the server's proof of `Rafthttp.sendable id m` for
   `Transport.Send.spec`'s premise (2d), and through it every stream delivery.
3. **No local message is sent**: `msgSent_type.spec` already bounds the type; rafthttp also needs
   that a sent message is not the link heartbeat (`MsgHeartbeat` from and to `0`): a node's
   messages are from its non-zero id, which item 2's `m.src = id` gives.

## from 2c

The read loop (`etcdserver/read`) uses R1's read API as stated (`readCtx_register`, `node.ReadIndex`,
`readState`, `readState_fire`, `readState_registered`, `committedLb_agree`, `committedOps_lb`): the
round's context registered with the update `readLbQ l` (result `⌜opsOf l <+: ops⌝`), fired by raft at
the committed operations of its confirmation. Nothing new is needed. The proposals' one-shot updates
(2c's `processInternalRaftRequestOnce`) need the server's raft cluster allocated with `dup = false`,
or the server's invariant firing only an entry's first committed occurrence (2d's).

## from 2d

Batch 2d (etcd's apply thread and raft node driver, `ApiApply.lean`):

1. **The term bound for the merged snapshot** (R1's item 10): `msgSent_replaceSnap` needs `s'.term
   ≤ m.term`. etcd's guard is `m.GetTerm() == apply.raftTerm` (the term of the latest hard state the
   loop handed out up to this batch); the applied term `appliedt` is at most it if **every committed
   entry and snapshot a `Ready` hands out has a term at most the batch's hard state's term**
   (`(b.hs.getD st.hs).term`). Please add it to `BatchOk` (or `readyGot`): it holds (raft's log
   terms are at most its current term, and a `Ready` reports a changed term in its `HardState`).
   ```go
   if m.GetTerm() == apply.raftTerm && m.GetSnapshot().GetMetadata().GetIndex() <= ep.appliedi {
       merged := s.createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)
   ```
   Used by: `createMergedSnapshotMessage.spec`, `applyAll.spec`.
2. **One-shot proposals**: etcd's raft cluster is allocated with `dup = false` (rafthttp never
   resends: 2f); 2c's at-most-once rests on it. Nothing new for R1.
3. **The restart's applied start**: etcd's `raftConfig` leaves `Applied = 0`, so `RestartNode`'s
   delivered log starts at the storage's offset, which is the `MemoryStorage` snapshot's index
   (bootstrap's `ApplySnapshot` then `Append`): `run`'s `etcdProgress` starts there. Nothing new.

## from 2e

1. **The restart snapshot's configuration.** `bootstrap` rebuilds the `MemoryStorage` of a restart
   from the WAL's newest valid snapshot record (index `si`, term) with the **backend's** configuration
   at its consistent index `ci ≥ si` (`bootstrap.go:107-115`, `buildConfStateFromV3store`), then hands
   it to `RestartNode`. `RestartNode.spec` takes `⌜σ.snap.isEmpty⌝ ∨ snapValid γ σ.snap`: with a conf
   change in `(si, ci]` that snapshot is not valid (R1's provability F3). Either `snapValid` (or a
   separate restart premise) admits "a snapshot at a committed index `si` with the configuration of a
   committed index `ci ≥ si`", or this is a finding (a follower sent that snapshot installs the
   configuration at `ci` with the log at `si`). Used by `bootstrap.spec`'s restart case,
   `memberDisk`'s realization.
2. `RestartNode.spec` at a configuration point `a` not bounded by the stored commit (R1 round 1, F1):
   relied on (a stop after the apply thread ran ahead of the raft loop's last `Save` of the commit).
