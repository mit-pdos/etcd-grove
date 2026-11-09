# Batch R2: raft's core (report)

Author agent, 2026-11-09. Everything builds: `etc/specs-build.sh` on `ApiCore` and the 61 spec
modules (62 modules, OK). Snippets: `examples/specreq/raftcore/*.go` (`//go:build ignore`, package
`raft`), gofmt clean, and `go vet` clean when copied into a scratch copy of the pinned raft module.

## Files

- `Spec/go_etcd_io/raft/v3/ApiCore.lean`: the vocabulary (below), its header (shape, intended
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

- **Internal steps whose correctness needs a guard only their caller's check establishes**, so that
  a spec over `raftCore` with an opaque, state-relative guard would be unsound or would fix the
  realization prematurely; each is part of its caller's proof sketch: `raft.send` (the queue's
  justification of the message), `sendHeartbeat`, `bcastHeartbeatWithCtx` (the context a pending
  read's), `reset`, `loadState` (run with the invariant open, inside `become*`/`newRaft`),
  `becomeCandidate`, `becomePreCandidate`, `campaign` (the campaign guard `hup` checked),
  `becomeLeader`, `poll` (the vote quorum), `appliedTo`, `appliedSnap` (the acknowledgement's
  evidence: inside `raft.Step`'s `ack` case), `switchToConfig` (inside `applyConfChange` and
  `appliedSnap`), `responseToReadIndexReq`, `sendMsgReadIndexResponse` (a read confirmed at a leader
  with an entry of its term committed).
- Asynchronous-writes only (unreachable under `ConfigOk`): `needStorageAppendMsg`,
  `newStorageAppendMsg`, `newStorageApplyMsg`.
- `DefaultLogger`'s methods and `header` (their contract is R1's `loggerOk`; its realization for
  `*DefaultLogger` needs Perennial's `log` model), `Status.MarshalJSON`/`String` (no caller in scope).

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
  **Met**, with one doubt for the reviewers: when `a > σ.last` (the node's log does not hold the
  entries up to `a`), the node may campaign with the configuration at `a`; it can only win with a
  log at least as up to date as a quorum of that configuration, so it then holds them. I found no
  counterexample, but the quorum-intersection argument across more than one configuration step is
  the place to check.
- **8b. A snapshot whose `ConfState` is taken at a committed point after its index**, installed at
  `Advance`: `appliedSnap` (after the fork's fix) restores the tracker from the snapshot's
  `ConfState` regardless of its index; no panic for a valid configuration (`confAt_valid`). Same
  shape as 8a; R2's `ackPost` gives R1's revised post (`∃ a m, nodeConf ⟨a, m⟩`, `s.index ≤ a`).
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

1. **The term (and index) bound.** `raft.Step` and the ticks take no term budget: each campaign (and
   each appended entry) takes a time receipt from raft's own steps, and the cluster invariant bounds
   terms and indices by the receipts. That needs the execution's step bound below `2^64 - 1` where
   the cluster is allocated (R1's `cluster_alloc.spec`, the bound's owner). Accept the receipt
   design (the old proof's, `budgetInv`), with the bound's fact entering at allocation?
2. **The `RawNode` phases** (`rawNodeAt`, `readyFresh`, `readyKept`, `readyHanded`, `ackOk`: five
   predicates) exist because `node.run` may send a `Ready` computed before other steps and because
   `acceptReady` panics on a second `Ready` before `Advance`. They are internal to the raft package
   (no client calls `RawNode`), but R1's `RawNode.Ready`/`HasReady`/`Advance` specs change to use
   them (request in `req/`). Acceptable, or should `RawNode`'s public specs hide them behind R1's
   `rawNode` (at the cost of `RawNode.Ready` needing a premise that no acknowledgement is queued)?
3. **Internal helpers left out** (list above): their specs need a guard only the caller's check
   establishes; stating them now would fix the realization's ghost state. Keep them out of the
   specs-only branch (specified with the proof), or state them over an internal, unsealed predicate?

## Findings for other batches

- **R1: `RawNode.Ready.spec` is unsound** (a second `Ready` after the first batch's `readyEnter` but
  before `Advance` panics in `acceptReady`). Fix proposed in `req/go_etcd_io_raft_v3.md` (R2,
  item 1). No bug in the Go code: `node.Ready` cannot reach it, and the panic is documented
  behaviour of `RawNode`.
- `lockedRand.Intn` ignores `crypto/rand.Int`'s error and dereferences the result: it rests on
  `rand.Reader` never failing (Go documents this since 1.24). Not a reachable bug; noted in the spec.
