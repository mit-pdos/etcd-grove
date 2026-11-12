# A4 (raft node API and core, batches R1, R2): provability verification

Reviewer: provability kind, independent. Commit under review: `1aa6fc1337` (`specs-only`).
Targets: `SpecPlan/Spec/go_etcd_io/raft/v3/{Model,Api,ApiCore}.lean` and the specs at the top level of
`SpecPlan/Spec/go_etcd_io/raft/v3/` of the functions of `node.go`, `rawnode.go`, `storage.go`,
`bootstrap.go`, `status.go`, `raft.go`, `state_trace_nop.go` and `logger.go`. That excludes R3's
`raftLog__*`, `unstable__*` and `readOnly__*`, and `util.go`'s functions. Snippets:
`examples/specreq/{raftnode,raftcore}/`. Callee specs cited: `ApiLog.lean` (R3), `tracker/`,
`quorum/`, `confchange/` (R4), `raftpb/` (3h).

I wrote all the findings below before reading `batch-R*.md`, `integration-*.md`,
`open-questions.md`, `reviews/` and the completeness report of this area. I read them afterwards
only to mark which findings were already recorded.

## Verdicts

| batch | verdict | first-tier findings |
|---|---|---|
| **R1** (`Model`, `Api`, `node`, `RawNode`, `MemoryStorage`, the starts, `Ready`) | **FAIL** | P1, P2, P3, P4 (P5 is R2's but blocks R1's `IsEmptyHardState`) |
| **R2** (`ApiCore`, `raft.go`, the `Ready` phases, loggers, tracing) | **FAIL** | P5; P3 is fixed in R2's `rawNodeAt_advance`. Open decision: the term/index receipt bound (R1 Q9, R2 Q1; `cluster_alloc.spec`'s docstring) |

Counts:
- **Specs checked:** 157 function specs (153 in the batch dump, plus `IsEmptyHardState`,
  `IsEmptySnap`, `isHardStateEqual` and `logSliceFromMsgApp`), plus every law in `Api.lean` and
  `ApiCore.lean`.
  - 146 close against the callee specs as they are now, apart from the shared open decision on the
    term bound (`raft.Step` and the ticks, `hup`, `campaign` and `becomeCandidate` rest on it).
  - 11 do not close: P1 (`readyChan_recv`, `ready_handout`, `RawNode.Ready`), P2
    (`raftState_crash`), P3 (`node.Advance`), P5 (`getLogger`, `SetLogger`, `ResetDefaultLogger`,
    `lockedRand.Intn`, `IsEmptyHardState`, `StateType.String`). Several others close only once P5 is
    fixed: `Config.validate` with a nil logger, `RawNode.Bootstrap`, `acceptReady`,
    `hasUnappliedConfChanges`.
- **Snippets checked:** 27 REQs (14 in `raftnode`, 13 in `raftcore`).
  - 21 close from the specs.
  - 4 do not: `ReqReadyLoop`, `ReqStartFresh`, `ReqLogger` (P4, P5) and `ReqBootstrap` (S1).
  - 2 need their `Assumes:` completed: `ReqReadyStale` and `ReqFields` (S2).
- **Laws checked:** all of them.
  - 3 cannot be proved jointly with the rest: `raftState_crash` (P2), and `raft_init`, whose
    statement lacks what its docstring promises (P5).
  - The remaining laws are plausible from the stated realization, and none makes the vocabulary
    vacuous. `confAt_valid` needs `Membership.empty` to be `Valid`, which R4 states.

## Can the stated realization (ApiCore's header) carry raft's safety?

Mostly yes. Here is the judgment for each property:

- **Election safety.** One vote per voter and term is made durable before any vote response is
  minted. `readyEnter` mints the `msgSent` of a `msgsAfterAppend` response only once the batch is
  durable. `readyCheck` releases messages early only when the batch ends with the node as leader.
  I checked that such a batch never carries a granted `MsgVote` response: `becomeLeader` happens
  only while `Advance` steps the self-vote (`rawnode.go:477-490`, `raft.go:1043-1091`), and a vote
  for another node ends the batch as follower. A leader may grant a pre-vote without
  `checkQuorum`, but a pre-vote changes nothing durable. With `leaderOf_agree`, this is plausible.
- **Log matching and leader completeness.** These follow from the per-term leader logs, with the
  lost send-before-write entries included, and from the durable-backed leader `Match`. Plausible,
  except across a crash: see P2(b).
- **Joint configurations and conf changes.** V1, V2 and V3, with `CampaignGuard` (`hup`,
  `raft.go:991-1011`; `promotable` includes the in-progress snapshot, `raft.go:1947-1950`), plus
  `committedLb_emptyV2` (validation on: `ConfigOk`). Plausible. I tried one route to a nil `pr` in
  `becomeLeader` (`raft.go:960`): a self-removal applied while the node is a candidate. It is
  unreachable. A candidate's commit does not move, a conf entry that is committed and not applied
  blocks `hup`, and `node.Advance` requires every delivered conf entry to be applied or decided
  skip.
- **Read index.** Item 3 plus the fork's single-voter fix. Two things the proof must do that the
  header leaves implicit. First, the ghost commit must step one index at a time and fire the
  persistent read update at each length, so that "fired when the log was `i` long" exists for the
  leader's commit `i`. Second, it must argue that at registration the ghost commit equals the
  leader's commit. That follows from the leader having committed an entry of its term together with
  the later quorum heartbeat, which excludes a newer leader. Plausible; worth a line in item 3.
- **Snapshots.** `snapValid`, `msgSent_snap`, `msgSent_replaceSnap` with the sender's delivered
  prefix and its term bound, and the view `a ≥ s.index`. Plausible.
- **Restart, crash and `confAboveOk`.** `confAboveOk` is the right condition for the reproduced bug
  (`issues/raft-commit-lost-with-entries-kept.md`).
  - Its realization needs a durable-state invariant that the header does not state: every
    `raftState γ id D` has at most one conf entry above `D.wcommit`. `RestartNode` lets the stored
    commit be as low as `wcommit` (`StorageHolds`), and V2 gives this invariant for every
    `Durable.next`.
  - The crash law as stated is not provable together with `BatchOk` (P2(a)).
  - The realistic crash leaves entries of a term above the durable term, which the header's
    invariants do not cover (P2(b)).

## First-tier findings

### P1. `BatchOk` is false for a `Ready` that carries a snapshot and the entries after it (Model.lean:379)

- **Principle.** Sound: a spec must be true of the code.
- **Evidence.**
  - `BatchOk` requires `b.ents ≠ [] → b.entsFrom ≤ st.durable.last + 1` even when
    `b.snap = some s`.
  - `unstable.restore` (`log_unstable.go:192-198`) sets `offset = s.index + 1`. A `MsgApp` at
    `prev = s.index` then appends `s.index + 1, …` to the unstable entries.
  - `readyWithoutAccept` hands out both in one `Ready` (`rawnode.go:143`, `:155`; `nextEntries`,
    `log_unstable.go:100-106`, is not blocked by the snapshot).
  - So `entsFrom = s.index + 1`. For a follower that was behind, `s.index` is far above
    `st.durable.last`.
  - Reachable trace:
    1. A lagging follower whose durable log ends at 10 restores `MsgSnap` index 100.
    2. Before its client takes the `Ready`, a new leader is elected whose last index is 100. Its
       first `bcastAppend` sends `MsgApp(prev 100, [101])` (`becomeLeader`'s empty entry).
    3. The follower accepts it (`raft.go:1806-1820`).
  - `Durable.next` handles this case correctly (it cuts at the snapshot's base), so only
    `BatchOk` is wrong.
- **Affects.** `readyGot` (hence `readyChan_recv`, `ready_handout`, `RawNode.Ready`) is
  unprovable. Snippets that install a snapshot and then append (`ReqReadyLoop`) are unaffected,
  because `readyStor_append` is right.
- **Fix.** Replace the clause with:

  ```
  b.ents ≠ [] → uint.nat st.hs.commit < b.entsFrom ∧
    b.entsFrom ≤ (match b.snap with | some s => uint.nat s.index | none => st.durable.last) + 1
  ```

  (With a snapshot it is in fact `= s.index + 1`.)

### P2. The crash law is not provable with `BatchOk`, and the header lacks the crashed node's term invariant (Api.lean:849-860)

- **Principles.** Sound; "A premise stated with a □∀ over states must be checked against the
  reachable states it does not pin down".

**(a) The old term with a raised commit.** `raftState_crash` allows `hs` with
`hs.term = st.durable.term ∧ hs.vote = st.durable.vote` together with any
`hs.commit ≤ (b.hs.getD …).commit` (the batch's commit) and `≤ crashed.last`.

- **Counterexample.**
  1. A follower at durable term `T` receives `MsgApp` of term `T' > T`. The batch has
     `hs = (T', 0, c)` and entries of term `T'`, with `c` covering some of them.
  2. The law lets the client keep the entries with `hs = (T, v, c)`.
  3. `RestartNode` from that state (`StorageHolds` holds) leads to a first `Ready` whose committed
     entries `(applied, c]` include term-`T'` entries, while `hs' = st.hs` has term `T`.
  4. `BatchOk`'s `∀ e ∈ b.committed, e.term ≤ hs'.term` (`Model.lean:382`) is then false. The law
     and `readyChan_recv` cannot both be proved.
- **No storage produces this hard state.** etcd's WAL writes the state record whole: entries, then
  state, then fsync. kvdurable's file does the same.
- **Fix.** Split the disjunction:
  - either the old record: `hs = ⟨D.term, D.vote, c⟩` with `D.wcommit ≤ c ≤ D.commit`;
  - or the batch's term and vote, with `D.wcommit ≤ c ≤` the batch's commit;

  each with `c ≤ crashed.last` and `confAboveOk`.

**(b) Even the realistic crash leaves entries above the durable term.** With the old record kept,
the restarted node's log holds entries of term `T' > T` and its term is `T`.
`integration-I2.md:147-151` records this fact for 2d's request, but not its consequence here.

- The header's realization has nothing that keeps `BatchOk`'s term clause true afterwards. Its
  items 1-2 and V3 talk only about quorums that committed.
- The clause stays true only if such a node cannot win an election at a term below `T'`.
- That needs the intersection of its candidacy quorums with the quorum that elected `T'`, across
  at most one conf entry above its commit (`confAboveOk`).
- **Fix.** Add this case to item 1 (or 4) of ApiCore's header: "a durable log may hold entries of a
  term above the durable term after a crash; such a node cannot win before that term, by
  intersection with the term's election quorum". Also add the durable invariant "at most one conf
  entry above `wcommit`" (the restart needs it, not only the crash).

**Status.** Not recorded. The crash law's open question (open-questions 2.8, R1 Q10) is about
`confAboveOk` and snapshot batches, not this.

### P3. `node.Advance`'s post has no source when the call returns (node__Advance.lean:49-62, ApiCore.lean:515-540)

- **Principle.** A premise or post with no source; a spec that is true needs its plan to close.
- **Evidence.**
  - `node.Advance` only sends on `advancec` and returns (`node.go:555-560`). The run goroutine
    runs `n.rn.Advance(rd)` after the rendezvous (`node.go:443-444`), concurrently with the
    returned caller.
  - The post (`nodeDriver {st with lastSnap := none}`, `appliedLb n st.delivered.length`, the
    snapshot's view wand) must therefore be produced at the send's linearization point.
  - `rawNodeAt_advance.spec` produces exactly these only in its closing, after every
    acknowledgement has been stepped and `ackDone` returned. Its opening gives the client nothing.
  - By the header's realization, `appliedLb` is R3's `logFloor` published by `raftLog_publish`.
    R3's premise (R3 provability round 1, F1) needs `i ≤ ls.applied`, which moves only when
    `MsgStorageApplyResp` is stepped.
- **Affects.**
  - `node.Advance` and its callers: `ReqReadyLoop`, etcd's `raftNode.start`, every example run
    loop.
  - `stor_compact`/`stor_createSnapshot` after `Advance` take that `appliedLb`. etcd's snapshot
    goroutine runs concurrently with `run`'s steps, through `raftAdvancedC`.
  - `RawNode.Advance` is synchronous and closes.
- **Fix.** Let `rawNodeAt_advance`'s **opening** give the client-facing half: the driver after
  `Advance`, `appliedLb rn st.delivered.length` and the snapshot-view wand. Keep for the closing
  only the struct's and the acknowledgements' bookkeeping. On R3's side:
  - `raftLog_publish` must accept `i ≤ ls.applying` with `handing = false` (after
    `raftLog_absorb`). The delivered entries are written and committed by then, and no raft read
    below them happens before the steps finish, because `run` is sequential.
  - V1 must tolerate the view having moved while the tracker's `appliedSnap` is still pending in
    `run` (no `ApplyConfChange` can reach `run` before that).

  Alternatively, realize the node-level predicates through a "pending `Advance`" state of the
  node's invariant. That still needs the R3 change.
- **Status.** Not recorded. The completeness report's F1 (snapshot before `Advance`) is related
  but distinct.

### P4. The `Ready`'s soft state, its read states, and `StartNode`'s peers cannot be read or built (Api.lean:165-171)

The completeness report found this as F2; I confirm it from the snippets. `softStateOpt`,
`readStatesRO` and `peersPts` are opaque, and their only law is persistence.

- **Snippets that fail:**
  - `ReqReadyLoop` reads `rd.SoftState`/`rd.RaftState` to decide whether to send before the write
    (`readyloop.go:57-59`). The `readyCheck` gate needs `lead` to equal
    `(b.soft.map (·.2)).getD st.role = StateLeader`.
  - `ReqStartFresh` passes a `[]raft.Peer` that the client cannot turn into `peersPts`
    (`restart.go:29-34`).
  - `ReqLinearizableRead` receives `raft.ReadState` values, which some loop must have read out of
    `rd.ReadStates`.
- **Fix.** Use the unfold and intro laws proposed in the completeness report's F2, or transparent
  definitions as for `hsOpt`/`snapOpt`.

### P5. `raft_init.spec` lacks the package variables that several specs read (ApiCore.lean:650-662)

- **Principle.** Every premise has a source. The README: "a fact about a package's globals after
  initialization is a law `X.init.spec`".
- **Evidence.**
  - The statement gives only `defaultLogger`, `discardLogger` and `globalRand`'s pointer. Its
    docstring promises "the logger guarded by `raftLoggerMu` meets `loggerOk` (its lock
    invariant)", which the formula does not contain.
  - Missing, with where each is read:
    - `raftLoggerMu`'s lock invariant (`raftLogger` meets `loggerOk`; `logger.go:44-58`, `:64-65`).
      Read by `getLogger`, `SetLogger`, `ResetDefaultLogger`, and `Config.validate` with a nil
      logger, so also `newRaft`, `NewRawNode` and the starts on the snippets' nil-logger configs.
    - `globalRand.mu`'s lock (`raft.go:93-104`), read by `lockedRand.Intn`. Its sketch says "its
      lock invariant in the package's initialization".
    - `emptyState ↦□ p ∗ hardStatePts p □ HardState.empty` (`node.go:32`). Read by
      `IsEmptyHardState` (`node.go:123`), `acceptReady`, and `RawNode.Bootstrap` (`bootstrap.go:48`,
      whose closing needs `hsPtr ph' □ empty` for exactly that pointer).
    - `stmap` (`raft.go:114`), read by `StateType.String`.
    - `errBreak` (`raft.go:1011`), compared in `hasUnappliedConfChanges`. Two loads must give the
      same value, otherwise the scan's `errBreak` panics (`Panicf`).
    - Outside A4, `util.go`'s `isLocalMsg`/`isResponseMsg` arrays, which `node.Step` and
      `RawNode.Step` call through `IsLocalMsg`/`IsResponseMsg`.
- **Affects.** `ReqLogger` (`raftcore/status.go`), `ReqMustSync`'s `IsEmptyHardState`, and through
  `IsEmptyHardState` every client `Ready` loop.
- **Fix.** Extend `raft_init.spec` with these, each persistent (a lock invariant through
  `is_Mutex`-style `isLock`).
- **Status.** `raftLoggerMu` and `globalRand` were raised in `reviews/R2-provability-1.md` 1.6 and
  2.6, and are still missing at HEAD. The others are new.

## Second-tier findings

- **S1. `ReqBootstrap` (`raftcore/ready.go:96-110`) asserts more than the specs give.**
  - The snippet checks `rn.raft.Term == 1` and `raftLog.committed == len(peers)` after
    `Bootstrap`. Neither `RawNode.Bootstrap.spec`'s post nor `rawNodeAt_core` (an existential
    view) relates the view to them, and no law reads `raftLog.committed`.
  - It also checks `len(rd.CommittedEntries) == len(peers)`. `readyGot`/`BatchOk` bound the
    committed entries only from above; `MaxCommittedSizePerReady` may split them.
  - Fix: either add the view to `RawNode.Bootstrap`'s post (term `1`, commit `|boot|`) or drop the
    checks. The second check is not a property callers rely on.
- **S2. Snippet assumptions.**
  - `ReqReadyStale` steps an arbitrary `m` with "Assumes: no acceptReady…". It needs `stepPre`
    of `m`.
  - `ReqFields` reads an arbitrary `m` ("Assumes: nothing"). It needs `msgPts` and a type in range
    for `IsResponseMsg`.
- **S3. Margins worth stating.**
  - `MemoryStorage.Entries` with `mx = 2^64-1 → es = rng` relies on `limitSize`'s running sum not
    wrapping (`util.go:286-305`). True in Go, unbounded in the model.
  - `Status.MarshalJSON` needs `RaftState < 4` for `%q` (through `stmap`), which `statusOwn` must
    carry. Its docstring should say so.
- **S4. ApiCore item 3** should say that the ghost commit is stepped one index at a time, with the
  read updates fired at each length (see the read-index paragraph above).

## Proof plans (every spec)

**Model and Api laws.**
- Allocation: `cluster_alloc`, `freshIds_take`, `bootLog_decided`.
- Committed log: `committedLb_*`, `committedOps_*`.
- Configurations: `confAt_*`, `confDecide`, `confDecided_agree`, `confDecisions_lookup`,
  `nodeConf_confAt`, `Membership.*`.
- Snapshots: `snap_make`, `snapValid_*`.
- Reads: `readCtx_register`, `readState_*`.
- Messages: `msgCredit_*`, `msgSent_*`.
- Nodes: `deliveredLb_*`, `nodeDriver_delivered`, `appliedLb_mono`, `storSnapLb_mono`,
  `rawNode_drop`, `zero_lbs`.
- Storage: `readyStor_install`, `readyStor_append`, `stor_*`.
- Go-level: `errs_init`, `errIs_*`, `memStor_isStorage`, `statusOwn_progress`,
  `bootEntryData_decode`, `isStorage_persistent`, `loggerOk_persistent`, `readyChan_recv`.

Each is plausible from the header's realization: ghost maps, mono-lists, R3's `logStorage` laws at
mask `⊤`, and the node's channel invariant (Perennial's select takes the clause pres conjunctively,
so `nodeDriver` survives a tick). The exceptions are `raftState_crash` (P2(a)) and
`readyChan_recv`/`readyGot` (P1). `memStor_isStorage`: `Term` needs `i < off + 2^63` (the `int`
conversion, `storage.go:Term`), which the slice length bound gives. `Entries` with `lo < hi ≤ last+1`
and `off < lo` excludes `ErrUnavailable`.

**MemoryStorage (11).** Under the mutex, the stated model update at the one store; the AU commits
there and aborts on the error paths. I checked each against `storage.go`:
- `Entries`: `lo ≤ off` gives `ErrCompacted`; `hi > last+1` is excluded by the pre; `len == 1`
  gives `ErrUnavailable`; otherwise `limitSize`, then `ents[:len:len]`.
- `Term`: the `int` conversion premise.
- `ApplySnapshot`: `EnsureSnapshot` on a full snapshot writes nothing; the clone; `ents` becomes
  the dummy.
- `CreateSnapshot`: its pre excludes both panics (`i > last`, and `i < off`, whose `i - offset`
  underflows); it writes `Metadata.ConfState` by replacing the pointer, so `InitialState`'s
  discarded `ConfState` share stays valid.
- `Compact`: the `make` capacity is `len - i`.
- `Append`: the four cases match `StorState.append` exactly, with `k + |es| < 2^64` preventing
  `last` from wrapping.
- `InitialState`, `SetHardState`, `FirstIndex`, `LastIndex`, `Snapshot`, `NewMemoryStorage`:
  trivial.

All close.

**Starts.**
- `newRaft`:
  - `validate`; `newLogWithSize` (R3); `InitialState` through `isStorage`; R4's `MakeProgressTracker`
    and `Restore` (`cf σ` `Is m`, `m.Valid` from `confAt_valid`); `switchToConfig` at the
    non-leader branch; `assertConfStatesEquivalent`.
  - `loadState`: its premise `committed ≤ hs.commit ≤ lastIndex` follows from `StorageHolds` plus
    the realization's `D.commit ≤ D.last`. An empty hard state forces `off = 0`, so the post's
    `ρ.hs = σ.hs` holds.
  - `appliedTo(Applied)`: needs `off ≤ Applied ≤ commit`, which is the pre.
  - `becomeFollower`; the client's AU fires at the `InitialState` read (`γ.ns` is not yet open).
  - `committedLb l`: from `snapValid σ.snap`'s prefix, plus `D`'s committed log up to `σ.hs.commit`.
  - Closes, given P5 for a nil logger.
- `NewRawNode`: `newRaft`, allocation, `softState`, `hardState`, `raftBoot_bind`. Closes.
- `RestartNode`: `NewRawNode`, `newNode`, `go run` (`nodeLoop`, `node.run.spec`). Closes.
- `setupNode`, `StartNode`: `NewRawNode` at the empty storage, then `RawNode.Bootstrap`. Close
  (given P5 for `emptyState`; P4 for the client's `peersPts`).
- `newNode`: channel allocations, `nodeFresh`. Closes.

**RawNode (19).**
- `Campaign`, `Propose`, `ProposeConfChange` (through `confChangeToMsg`), `ReadIndex`,
  `ReportUnreachable`, `ReportSnapshot`, `TransferLeader`, `ForgetLeader`, `Tick`, `Step`: each is
  `rawNodeAt_core`, then `raft.Step` with `stepIn` (the proposal, read, report and received cases
  each match the `pb.Message` literals at `rawnode.go:83-557`), then close. `RawNode.Step` refuses
  local messages and responses from unknown peers first; a `msgSent` message is never local (an
  internal fact of `msgSent`).
- `Ready`: `readyWithoutAccept`, `ready_handout`, `acceptReady` (fails with P1).
- `readyWithoutAccept`: R3's `next*` and the getters, at `readyFresh`.
- `acceptReady`: needs `emptyState` (P5).
- `HasReady`: with `readyKept`, by item 6's monotonicity. I checked that a step cannot take
  `HasReady` from true to false without an accept: `msgs`, `msgsAfterAppend` and `readStates` only
  grow; the hard state does not return; a restore that hides committed entries shows a snapshot;
  a soft-state return comes with a heartbeat response.
- `Advance`: `rawNodeAt_advance`, `raft.Step` with `StepSrc.ack` for each acknowledgement, then
  close.
- `ApplyConfChange`: `raft.applyConfChange`.
- `Bootstrap`: `rawNodeAt_bootstrap`, the storage's `LastIndex = 0`, `proto.Marshal` of the
  `AddNode` (3h's `bootCC_facts`), R3's `append` and the commit, then `applyConfChange` per peer
  (the decided `.v1` with context equals the context-less `AsV2` under `applyChange`). Closes given
  P5.
- `Status`, `BasicStatus`: `getStatus`/`getBasicStatus` on `raftRO`.
- `applyUnstableEntries`: trivial.

**node (17).**
- `step`, `stepWait`, `stepWithWaitOption`:
  - Non-`MsgProp` goes to `recvc`; `MsgProp` goes to `propc`, plus a `result` channel when
    waiting. `ctx.Done()` comes from W0's `Context.Done`.
  - The channels' invariants carry `stepOk`, and `run` rewrites `From` (`node.go:388`), which
    `stepIn`'s "up to the sender" case covers.
  - Errors are `nodeErr`, plus `ErrProposalDropped` from `result`.
- `Step`: a nil message gives the "nil message" error (excluded by `msgRecv`); a local message
  returns nil, otherwise `step`. Closes.
- `Propose`: `stepWait`. `ProposeConfChange`: `confChangeToMsg`, then `Step` (no wait, so no
  `ErrProposalDropped`). `Campaign`, `ReadIndex`, `ForgetLeader`, `TransferLeadership`,
  `ReportUnreachable`, `ReportSnapshot`, `Tick` (the default branch reads the persistent `id` and
  `logger`): one channel operation each. All close.
- `Ready`: a field read. `Status`: `status` channel, then `getStatus`. `Stop`: `stop`/`done`
  (gives `nodeVacant` when running).
- `ApplyConfChange`: `confc`, where `run` calls `raft.applyConfChange`, then `confstatec`. `done`
  cannot close in between, since only `run` closes it. Closes.
- `Advance`: **fails, P3.**
- `run`: the loop invariant is `nodeLoop` with `rawNodeAt`. Each arm uses `HasReady` with
  `readyKept`, `readyFresh_ro`/`raftRO_peek` for the field reads, `ready_handout` inside the send
  (with the receiver's driver), `acceptReady`, `RawNode.Advance`, `applyConfChange` and
  `getStatus`. Closes as a plan, given P1 and P3.

**raft.go (49).**
- `raft.Step`: the term switch, then `hup`, the vote rule (`isUpToDate`, R3), the acknowledgement
  handlers (`stableTo`, `appliedSnap` (a non-leader: an in-progress snapshot blocks `promotable`),
  `appliedTo`, `reduceUncommittedSize`), then `step*`. Rests on the term bound.
- `stepLeader`, `stepFollower`, `stepCandidate`: by message type over the helpers below. I checked
  the `stepCandidate` arms (`raft.go:1688-1730`). Each closes over the helpers' specs.
- `send`: the `sendShape` checks are exactly `raft.go:514-540`'s panics.
- `sendAppend`, `maybeSendAppend` (`pr` non-nil by the `prs` premise), `maybeSendSnapshot` (its
  two panics are excluded by `isStorage`'s `Snapshot` contract and `stor_read`'s `off ≤ snap.index`
  plus a leader having no unstable snapshot), `sendHeartbeat` (`min(Match, committed)`),
  `bcastAppend`, `bcastHeartbeat`, `bcastHeartbeatWithCtx`, `sendTimeoutNow`: close.
- `appliedTo`, `appliedSnap` (the fork's switch at apply), `maybeCommit`, `reset`, `appendEntry`
  (the receipt per entry), `tickElection`, `tickHeartbeat`: close.
- `becomeFollower`, `becomeCandidate` (the receipt), `becomePreCandidate`, `becomeLeader` (the
  empty entry is never dropped: payload `0`), `hup`, `campaign`, `poll`: close.
- `hasUnappliedConfChanges`: needs `errBreak` (P5).
- `promotable`, `committedEntryInCurrentTerm`, `pastElectionTimeout`,
  `resetRandomizedElectionTimeout` (needs `globalRand`'s lock, P5), `abortLeaderTransfer`,
  `increaseUncommittedSize`, `reduceUncommittedSize`: close.
- `handleAppendEntries` (`logSliceFromMsgApp`, `maybeAppend`, `findConflictByTerm`),
  `handleHeartbeat` (`commitTo` within the last index: `Match` is durable-backed), `handleSnapshot`,
  `restore`, `applyConfChange` (R4's `Changer`; `panic(err)` is excluded by `applyChange = some`),
  `switchToConfig`, `loadState`: close.
- `responseToReadIndexReq`, `sendMsgReadIndexResponse`, `releasePendingReadIndexMessages`: close.
- `hardState`, `softState`, `hasLeader`, `Config.validate` (given P5 for a nil logger),
  `lockedRand.Intn` (P5), `StateType.String` (P5): as noted.
- `getStatus`, `getBasicStatus`, `getProgressCopy`, `Status.String`, `Status.MarshalJSON`: close
  (S3).
- The `need*`/`newStorage*` helpers are reachable only with `AsyncStorageWrites`, which `ConfigOk`
  excludes. Their posts are true of the code.
- `MustSync`, `SoftState.equal`, `isHardStateEqual`, `IsEmptySnap`: close. `IsEmptyHardState`: P5.
- The 11 `trace*` are no-ops. `header`, and the 14 `DefaultLogger.*` (frozen fields; `Panic`/`Fatal`
  under `False`), close. `SetLogger`, `getLogger`, `ResetDefaultLogger`: P5.

## Snippets

| file | REQ | closes? | how |
|---|---|---|---|
| raftnode/propose.go | ReqProposeOnce, ReqProposeRetry | yes | `propErr` with `errs_init`; `□?γ.dup` |
| raftnode/readindex.go | ReqLinearizableRead | yes, given P4 for the `states` feeder | `readState_fire` with the client's `Q` recording its write; `readState_registered` |
| raftnode/readyloop.go | ReqReadyLoop | **no (P4, P3; P1 under its spec)** | Invariant: `applied = st.delivered.length`, `lead ↔ st.role = Leader`, the view at `applied`, conf entries applied or decided skip. Pieces: `readyCheck`/`readyEnter`, `readyStor_install`/`_append`, `stor_setHardState`, `node.ApplyConfChange` (its `nil` disjunct is excluded by the loop's `nodeRunning` share), `node.Advance` |
| | ReqMustSync | yes, given P5 | `IsEmptySnap`, `IsEmptyHardState`, `MustSync` |
| | ReqDisrupt | yes | the error specs; `Status().Lead` is a value field |
| raftnode/restart.go | ReqStartFresh | **no (P4: `peersPts`)** | otherwise `ConfigOk`, a nil logger, `memStor_isStorage` |
| | ReqRestartDurable, ReqJoin, ReqStopRestart | yes | `StorageHolds` at `Durable.init` for the empty storage; `confAt γ 0 empty`; `Stop` with `running = false` |
| raftnode/confchange.go | all 4 REQs | yes | `committedLb_confDecodes`, `applyChange_v1` at node `0`, `committedLb_emptyV2` with the client's ops invariant (`committedOps_lb`) |
| raftnode/storage.go | all 4 REQs | yes | the `MemoryStorage` specs; AU-in-AU wrapping of `stor_read` around `FirstIndex`/`Snapshot` (two reads chained by `storSnapLb`); `stor_createSnapshot` matches `CreateSnapshot`'s pre case by case. (`ReqSnapshotCompact`'s assumption is the completeness report's F1.) |
| raftnode/transport.go | ReqDeliver, ReqSendSnapshot | yes | `node.Step` with `msgRecv` of the clone; `msgSent_replaceSnap` |
| raftcore/step.go | all 7 REQs | yes (`ReqTick` under the term bound) | `stepIn`'s four cases and `raft.Step`'s error post |
| raftcore/ready.go | ReqReadyAdvance, ReqReadyPeek, ReqNewRawNode | yes | from the specs (but `ready_handout` itself fails with P1) |
| | ReqReadyStale | assumption missing (S2) | `readyFresh_forget`, `HasReady` gives `readyEmpty` |
| | ReqBootstrap | **no (S1)** | |
| raftcore/conf.go | ReqApplyConf | yes | `raftpb_ne_null` |
| raftcore/status.go | ReqStatus, ReqTickMissed | yes | |
| | ReqFields | assumption missing (S2) | |
| | ReqLogger | **no (P5)** | |

## Targets ranked by need of revision

1. `Api.lean`'s `raftState_crash`, and `ApiCore.lean`'s header items 1 and 4 (P2).
2. `ApiCore.lean`'s `rawNodeAt_advance`, with R3's `raftLog_publish` (P3), which unblocks
   `node.Advance`.
3. `Model.lean`'s `BatchOk` (P1).
4. `ApiCore.lean`'s `raft_init` (P5).
5. `Api.lean`'s `softStateOpt`, `readStatesRO` and `peersPts` (P4).
6. The `ReqBootstrap`, `ReqReadyStale` and `ReqFields` snippets (S1, S2), and the docstrings (S3,
   S4).

## Go code

I found no bug in the Go code. The crash behavior in P2(b) is the known
`issues/raft-commit-lost-with-entries-kept.md` scenario's companion (the WAL keeps entries with an
older state record). That is a spec gap, not a new Go bug, so nothing goes into `issues/`.
