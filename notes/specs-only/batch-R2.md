# Batch R2: raft's core (report)

Author agent, 2026-11-09. Everything builds: `etc/specs-build.sh` on `ApiCore` and the 61 spec
modules (62 modules, OK). Snippets: `examples/specreq/raftcore/*.go` (`//go:build ignore`, package
`raft`), gofmt clean, and `go vet` clean when copied into a scratch copy of the pinned raft module.

## Files

- `SpecPlan/Spec/go_etcd_io/raft/v3/ApiCore.lean`: the vocabulary (below), its header (shape, intended
  realization, snippets) and its laws.
- Client-facing (R1's callers): `newRaft`, `raft__Step`, `raft__tickElection`, `raft__tickHeartbeat`,
  `raft__applyConfChange`, `raft__hasLeader`, `raft__softState`, `raft__hardState`, `getStatus`,
  `getBasicStatus`, `getProgressCopy`, `Config__validate`, `SetLogger`, `getLogger`,
  `ResetDefaultLogger`.
- rawnode.go's internals R1 left to R2: `RawNode__readyWithoutAccept`, `RawNode__acceptReady`,
  `RawNode__applyUnstableEntries`, `needStorageAppendRespMsg`, `newStorageAppendRespMsg`,
  `newStorageApplyRespMsg`.
- raft.go's internal helpers: `stepLeader`, `stepCandidate`, `stepFollower`, `raft__hup`,
  `raft__becomeFollower`, `raft__handleAppendEntries`, `raft__handleHeartbeat`,
  `raft__handleSnapshot`, `raft__restore`, `raft__appendEntry`, `raft__maybeCommit`,
  `raft__bcastAppend`, `raft__bcastHeartbeat`, `raft__sendAppend`, `raft__maybeSendAppend`,
  `raft__maybeSendSnapshot`, `raft__sendTimeoutNow`, `releasePendingReadIndexMessages`,
  `raft__pastElectionTimeout`, `raft__resetRandomizedElectionTimeout`, `raft__abortLeaderTransfer`,
  `raft__promotable`, `raft__hasUnappliedConfChanges`, `raft__committedEntryInCurrentTerm`,
  `raft__increaseUncommittedSize`, `raft__reduceUncommittedSize`, `logSliceFromMsgApp`,
  `lockedRand__Intn`, `StateType__String`.
- Tracing (`state_trace_nop.go`, no-ops): `traceInitState`, `traceReady`, `traceCommit`,
  `traceReplicate`, `traceBecomeFollower`, `traceBecomeCandidate`, `traceBecomeLeader`,
  `traceChangeConfEvent`, `traceConfChangeEvent`, `traceSendMessage`, `traceReceiveMessage`.
- Snippets `examples/specreq/raftcore/`: `step.go` (every source of a step; the only error is a
  dropped proposal; ticks), `ready.go` (Ready, writes, Advance's acknowledgements, a second Ready
  only after Advance; `node.run`'s stale Ready; `NewRawNode`'s construction), `conf.go`
  (`applyConfChange`), `status.go` (getters, `node.run`'s field reads, the logger).
- Requirement notes appended/created: `req/go_etcd_io_raft_v3.md` (`## from R2`: to R1 and R3),
  `req/go_etcd_io_raft_v3_tracker.md`, `req/go_etcd_io_raft_v3_quorum.md`,
  `req/go_etcd_io_raft_v3_confchange.md`, `req/go_etcd_io_raft_v3_raftpb.md`.

## Exported vocabulary (`ApiCore.lean`, namespace `Raft`)

Pure: `CoreView` (hard state, leader, role, progress map: what callers read), `StepSrc` (`outside`
or `ack rn st k v`), `isReportType`, `localAppendThread`, `localApplyThread`.

Predicates:
- `raftCore r γ id ρ` (excl): the raft struct with everything inside (log, tracker, read-only queue,
  queued messages, the node's protocol state). The one token R1 asked for.
- `raftOf rn r` (transparent, pers): `rn.raft ↦□ r`.
- `raftBoot r γ ρ st v S i j` (excl, one-shot): `newRaft`'s node-level start state, before a
  `RawNode` exists.
- `raftPeek r id ρ mp` (transparent): the fields `node.run`/`node.Tick` read (`id`, `logger`, `lead`,
  `Term`, `trk.Progress`, `tick`).
- `propUpd γ e` (transparent): the client's update for a proposed entry.
- `stepIn γ id m` (transparent): a message's provenance (received with `msgSent`/credit/address; local
  proposal with updates; local read with its `readCtx`; local timer/report).
- `ackOk rn γ m` (excl), `ackPre`, `ackPost` (transparent): an acknowledgement `acceptReady` queued,
  what stepping it needs (the batch entered and written: R1's driver and `readyStor`) and gives
  (applied index, a snapshot's configuration).
- `stepPre`, `stepPost` (transparent): `raft.Step`'s pre/post by source.
- `rawNodeAt rn γ id k adv` (excl): R1's `rawNode` after `k` accepted `Ready`s, acknowledgements
  queued iff `adv`. `readyFresh rn γ id k adv rd` (excl): with `rd` its current `Ready`.
  `readyKept rn k rd` (pers). `readyHanded rn γ id k rd` (excl): handed out, `acceptReady` due.
- `leaderOf γ t l` (pers, internal): `l` won term `t`.
- Provisional raftpb/tracker ownership: `entryPtrs sl dq es` (3h's), `progressCopyOwn mp` (R4's).

Laws: `core_persistent`, `raftCore_exclusive`, `leaderOf_agree` (election safety),
`msgSent_leaderOf` (appends, heartbeats, snapshots, `MsgTimeoutNow` come from the term's leader),
`raftCore_peek` (field reads), `raftBoot_bind` (a fresh raft struct into its `RawNode`: `rawNodeAt
... 0 false` and R1's node predicates keyed by `rn`), `rawNode_at` (R1's `rawNode` is `rawNodeAt`
at some phase), `rawNodeAt_core` (open the raft struct; close at any view), `rawNodeAt_advance`
(the queued acknowledgements, each `ackOk`; an emptied queue gives `adv = false`),
`readyFresh_forget`, `ready_handout` (a fresh `Ready` with nothing queued, at the driver: R1's
`readyGot`, leaving `readyHanded`).

## Main decisions and changes from the old specs

- **`raft.Step` has one precondition, the message's provenance, and needs no scope extension.** The
  old `raft__Step` (775 lines, 48 revisions) stated the node's whole state (`NState`) and frames
  (`LocalFrame`, `NetFrame`, `TermStep`, `RespStep`, `SnapStep`, `PreCandStep`) and transport
  premises (`RestMsgOk`: a stamped `MsgTransferLeader`'s receiver, a `MsgTimeoutNow`'s term budget).
  Now: the protocol's facts live in R1's opaque cluster vocabulary (`msgSent` records each message's
  protocol fact; `committedLb`, `confAt`, `readState`, `raftState`), the term budget is the cluster's
  (receipts), and what the `RawNode` layer needed from the frames is its phase predicates. Every
  message type and feature (PreVote, CheckQuorum, learners, leader transfer, joint consensus,
  snapshots, stale terms) is covered by `stepIn`'s four cases or an `ackOk`.
- **The `Ready` protocol is stated at the `RawNode` level** (R1 left `readyWithoutAccept` and
  `acceptReady` to R2): fresh / kept / handed / accepted phases. They make `node.run`'s stale send
  (a `Ready` computed before other steps, sent when `HasReady()` is false) provable, and exclude
  the second-`Ready`-before-`Advance` panic.
- **Keys.** The raft struct's own predicates are keyed by `r`; node-level effects (`applyConfChange`,
  acknowledgements, binding) are stated with R1's predicates keyed by the `RawNode` `rn` and
  `raftOf rn r`, because `newRaft` runs before the `RawNode` exists.
- `ReadOnlyLeaseBased`, `AsyncStorageWrites`, `DisableConfChangeValidation` stay as R1 left them
  (`ConfigOk`): a lease read needs a clock model raft's specs do not have.

## Left out

Nothing of `raft.go`, `logger.go`, `status.go` or the `rawnode.go` internals R1 left (round 1 added
the fifteen internal helpers, the three asynchronous-writes helpers, `DefaultLogger`'s methods,
`header`, `Status.MarshalJSON` and `Status.String`). Not specified: `RawNode.TickQuiesced` and
`RawNode.WithProgress` (R1's functions, no user in scope; the laws they would need are noted in
`req/`).

## R1's added obligations (`req/go_etcd_io_raft_v3.md`, items 8-10): does raft.go meet them?

Traced through `newRaft`, `restore`, `appliedSnap`, `switchToConfig`, `hup`, `stepLeader`:

- **8a. Restart at a configuration point `a` above the stored commit.** No panic depends on it:
  `newRaft` restores the tracker from `cf σ` with `confchange.Restore` (only `LastIndex` used for the
  progress), `loadState` checks only the commit against the log, and `hasUnappliedConfChanges` scans
  `(applied, committed]`, all below `a`. For safety the invariant has the shape of a node that has
  applied further than it has committed: its tracker at `confAt γ a m` with `a` committed in the
  cluster, at least the applied index. The configuration counts votes and acknowledgements only
  when the node is candidate or leader; a leader holds every committed entry (leader completeness),
  so a leader using the configuration at a committed `a` is as a leader that applied to `a`; a
  candidate's quorum is of a committed configuration at or after every configuration it could have
  applied. The conf entries in `(commit, a]` are later re-delivered below the view and must be
  no-ops (R1's `ApplyConfChange` else-branch), which R2's `raft.applyConfChange.spec` keeps.
  **Met.** Round 1: the doubt (a view past the node's log's end) is closed by the provability
  reviewer's argument, now the realization's item 4 in `ApiCore.lean` (V1-V3: a candidate whose view
  is ahead of its log's end cannot win, since every quorum of its view holds an entry past that end).
- **8b. A snapshot whose `ConfState` is taken at a committed point after its index**, installed at
  `Advance`: `appliedSnap` (after the fork's fix) restores the tracker from the snapshot's
  `ConfState` regardless of its index; no panic for a valid configuration (`confAt_valid`). Same
  shape as 8a; `rawNodeAt_advance`'s closing gives R1's revised post (the client-chosen view wand).
  `restore` refuses a snapshot whose configuration does not list the node (liveness only). **Met**
  (same caveat).
- **9. The stored snapshot stays empty or valid**, and `maybeSendSnapshot` sends only valid ones:
  raft's `snapshot()` returns the unstable snapshot (received in a `MsgSnap`: `msgSent_snap`) or the
  storage's (`stor_read`'s guarantee; the storage's only writers are R1's updates, each storing a
  valid snapshot); `IsEmptySnap` cannot fire, since `term(Next - 1)` fails only below the
  compaction point, which `stor_compact` keeps at most the stored snapshot's index. **Met.**
- **10. `msgSent_replaceSnap` with a prefix of the sender's delivered log.** The follower's
  `MsgAppResp` after restoring the replaced snapshot acknowledges its index `i`; the delivered log is
  committed and a prefix of the leader's log at its term (a leader of term `t` holds every entry
  committed while it leads), so the follower's log up to `i` is the leader's and the leader's
  `MaybeUpdate(i)` is sound; a response that arrives after the leader's term ended is stale and
  ignored (`raft.Step`'s lower-term branch). **Met.**

## Open questions for the user

1. **The term (and index) bound.** `raft.Step` and the ticks take no term budget: each term increase
   and each appended entry deposits a time receipt from raft's own steps, and the cluster invariant
   bounds terms and indices by the receipts (realization item 5). That needs the execution's step
   bound (at most `2^63`, which also covers R3's range premises) where the cluster is allocated:
   R1's `cluster_alloc.spec`, requested (`req/go_etcd_io_raft_v3.md`, round 1, item 7). Both
   reviewers judged the design sound. Accept?
2. **The `RawNode` phases** (R1 has adopted them): no question left.
3. **The internal layer** (`raftOpen`, `coreInv`, `coreInvConf`, `msgJust`, `voteFrom`,
   `readConfirmed`, `leaderOf`, `CoreOpen`, `CampaignGuard`): stated now, as both reviewers asked,
   marked internal. Their realization (what `coreInv` is) is the header's; the specs over them fix
   the Go-level split and the callers' checks, not the ghost state's layout.

## Findings for other batches

- **R1: `RawNode.Ready.spec` is unsound** (a second `Ready` after the first batch's `readyEnter` but
  before `Advance` panics in `acceptReady`). Fix proposed in `req/go_etcd_io_raft_v3.md` (R2,
  item 1). No bug in the Go code: `node.Ready` cannot reach it, and the panic is documented
  behaviour of `RawNode`.
- `lockedRand.Intn` ignores `crypto/rand.Int`'s error and dereferences the result: it rests on
  `rand.Reader` never failing (Go documents this since 1.24). Not a reachable bug; noted in the spec.

## Round 1 repairs

Reviews: `reviews/R2-provability-1.md`, `reviews/R2-completeness-1.md`. Everything rebuilt
(`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/raft/v3`, R1's and R3's files included); snippets gofmt
clean and `go vet` clean in a scratch copy of the pinned raft module.

First tier:
- **The fifteen helpers** (provability 1.1, completeness F7) are specified over the internal layer
  (`ApiCore.lean`, "Internal"): `raftOpen r γ id o` (the struct opened, at `o : CoreOpen`: the view,
  R3's `LogState`, R3's `ReadOnlyState`, the scalars), `coreInv r γ id o` (the invariant's
  condition), `raftCore_open`/`raftCore_close`, `raftOpen_log`, `raftOpen_ro`. Each takes its
  caller's check, per the completeness table: `send` (`sendShape`, `msgJust`), `sendHeartbeat` and
  `bcastHeartbeatWithCtx` (leader, the read-only queue's context `hbCtxOf`), `appliedTo` (within the
  commit; at a leader, the invariant at the new applied index, for the auto-leave step),
  `appliedSnap` (`snapValid`, R3's `SnapAckOk`, not a leader), `reset`, `loadState` (`committed ≤
  hs.commit ≤ lastIndex`), `becomeCandidate`/`becomePreCandidate`/`campaign` (not a leader,
  `CampaignGuard`, or a pre-candidate's won pre-vote), `becomeLeader` (a candidate with a progress,
  `leaderOf`), `poll` (`voteFrom`; `VoteWon` gives `leaderOf`), `switchToConfig` (R4's result,
  `trkResult`; at a leader `coreInvConf`), `responseToReadIndexReq` (`readConfirmed`; the local or
  forwarded answer), `sendMsgReadIndexResponse` (leader, an entry of its term committed). Also
  specified: the asynchronous helpers (`needStorageAppendMsg`, `newStorageAppendMsg`,
  `newStorageApplyMsg`), `DefaultLogger`'s methods (`defaultLoggerOk`/`defaultLoggerOwn`, `Fatal*`/
  `Panic*` with pre `False`), `header`, `Status.MarshalJSON`, `Status.String`.
- **Results stated** (provability 1.2, completeness F8): `promotable`, `hasUnappliedConfChanges`,
  `committedEntryInCurrentTerm`, `pastElectionTimeout` are over `raftOpen` with their result exact
  over `o` (`CampaignGuard` is what `hup`'s checks give); `maybeCommit` says whether the commit moved;
  `restore` states the commit (and its index when it replaces the log); `newStorageAppendRespMsg`
  states the acknowledged entry id (provability 2.1).
- **Forwarded proposals** (completeness F1): `stepIn`'s received case is up to the sender for a
  `MsgProp` (`node.run` rewrites `From`); snippet `ReqStepForwardedProposal`.
- **`Advance`** (provability 1.4, 1.7; completeness F2, F3): `rawNodeAt_advance` takes R1's `Advance`
  pre (driver, storage writes done, view, `confSkipped`), gives the struct with the released
  acknowledgements (`ackOk`), and its closing (the struct at any view, the emptied field, an `ackDone`
  per acknowledgement) gives R1's `Advance` post exactly, the snapshot arm with R1's client-chosen
  view wand. `ackOk_type`: acknowledgements are never proposals. `StepSrc.ack rn` carries no driver
  any more; `ackPre`/`ackPost` removed.
- **Reads between computing a `Ready` and sending it** (completeness F4): `raftRO` (a read-only share
  at a view), `raftCore_ro`, `readyFresh_ro`; the getters and the field reads (`raftRO_peek`) take
  `raftRO`. Snippet `ReqReadyPeek`.
- **`RawNode.Bootstrap`** (completeness F5): `rawNodeAt_bootstrap` (the window: the struct open at the
  empty log with `coreInv`, `prevHardSt`, `committedLb γ boot`; closed after `becomeFollower(1)` and
  the entries appended and committed; then `applyConfChange` per peer on the closed struct);
  `raft.applyConfChange.spec` takes `committedLb γ l` (was `deliveredLb rn γ l`; R1's callers derive
  it); `becomeFollower` is over the opened struct. R1 asked for the bootstrap decisions' law.
  Snippet `ReqBootstrap`.
- **`newRaft`'s post** keeps `validate`'s relation (`Config.defaulted`, completeness F6); `ReqNewRawNode`
  reads `AsyncStorageWrites` back.
- **`HasReady = false`** (provability 1.5, (d)): `readyEmpty` (`ApiCore.lean`) and the monotonicity
  fact (realization item 6); R1 asked to add `readyEmpty rd` to `HasReady`'s `false` case.
  `ReqReadyStale`'s header corrected (the stale `Ready` is empty, soft state included).
- **`loggerOk ⇒ non-nil`** (provability 1.6): `loggerOk_nonnil.spec`; `raft_init.spec` (default
  loggers, `globalRand`), `defaultLogger_loggerOk.spec`.
- **The term bound** (provability 1.3): requested of R1 (`cluster_alloc`, a bound of `2^63`, as R3
  asked); realization item 5 names the owner's protocol and the bootstrap offset (2.4).
- **The realization** (provability (a), 2.2, 2.3, 2.5): `ApiCore.lean`'s header now states
  `raftCore`'s definition over `raftOpen`/`coreInv` and the invariant's items: per-term leader logs
  and election safety, durable responses and replaced snapshots, reads (deposited at the first step,
  fired at every commit: the old proof's scheme, not at confirmation), configurations (V1-V3), the
  term bound, and the `Ready` phases (`readyKept` keeps no memory; the `HasReady` monotonicity).

Second tier: line citations corrected in the specs and snippets; the copied "Users" sentence of the
send helpers replaced per function; snippets for a conf-change proposal (`ReqStepConfChange`) and a
transfer with its target (`ReqStepReports`), `ReqTickMissed` (completeness S4); `ReqStatus` no
longer writes the returned hard state; requests to 3h (a field-write law for `msgPts`,
`confStatePts`'s non-null law) and R4 (`trkResult`). Not done: `TickQuiesced`/`WithProgress` laws
(S3; no user), moving `leaderOf`/`msgSent_leaderOf` to a separate internal module (2.8; marked
internal, for `etc/api`).

R3's revised log vocabulary (`ApiLog.lean`) is what the internal layer is stated over (`LogState`,
`termOf`, `range`, `lastIndex`, `appliedTo`, `SnapAckOk`, `ReadOnlyState`); `raftOpen_log` exposes
R3's `raftLog`.
