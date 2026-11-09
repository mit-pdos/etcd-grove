/-
# Raft's core (batch R2): the vocabulary of the `raft` struct

What the node API (R1: `Api.lean`, `Model.lean`; `RawNode`'s and `node`'s proofs) uses of the raft
state machine in `raft.go`: one exclusive token for the raft struct, the provenance of a message it
steps, and the `RawNode`-level phases of a `Ready` (computed, handed out, accepted, its
acknowledgements stepped at `Advance`); and, marked internal, the layer `raft.go`'s own helpers are
specified over (the struct with its invariant opened). The specs of the functions are the files
beside it (`newRaft.lean`, `raft__Step.lean`, `RawNode__acceptReady.lean`, ...).

## The shape, in words

**The raft struct** `r` of node `id` of cluster `γ` is `raftCore r γ id ρ`: exclusive, created by
`newRaft`, held inside the `RawNode` around it (`rawNodeAt`, R1's `rawNode`). `ρ : CoreView` is only
what its callers read of it with Go field reads or getters: the hard state (term, vote, commit), the
leader, the role and the progress map. A read-only share `raftRO r id ρ` (`raftCore_ro`) is what the
getters and the field reads take, so that they can run while a `Ready` is fresh (`readyFresh_ro`).
Everything else (the log, the tracker, the read-only queue, the queued messages, the protocol's
ghost state) is inside the token, and **`raft.Step` keeps the token for every message, every state
and every feature** (PreVote, CheckQuorum, learners, leader transfer, joint consensus, snapshots):
its precondition is only the message's provenance (`stepIn`: received with its `msgSent` and credit
-- a proposal up to its sender, which `node.run` rewrites; a local proposal with its client's
updates; a local read with its registered context; a local report or timer message; or an
acknowledgement `ackOk` that `rawNodeAt_advance` released), and its post says only what callers
inspect (the error is `ErrProposalDropped` for a dropped `MsgProp`, `nil` otherwise). The protocol's
safety is not stated per step: it is the meaning of R1's cluster vocabulary (`committedLb`,
`confAt`, `readState`, `msgSent`, `raftState`), which `raft.Step` keeps true, and of the `Ready`
raft hands out (R1's `readyGot`).

**Binding to a `RawNode`.** `newRaft` cannot know the `RawNode` it will be in (`NewRawNode`
allocates it after). It returns the node-level start state as a one-shot `raftBoot r ...`; once the
`RawNode` `rn` holds `r` in its `raft` field (`raftOf rn r`, persistent), `raftBoot_bind` turns it
into R1's node predicates keyed by `rn` and into `rawNodeAt rn γ id 0 false`. The raft struct's
methods that move node-level state (`applyConfChange`, `appliedTo`) take R1's predicates keyed by
`rn` with `raftOf rn r`. `RawNode.Bootstrap` opens the fresh struct through `rawNodeAt_bootstrap`.

**The `Ready` phases** (`rawnode.go`'s internals). `rawNodeAt rn γ id k adv` is R1's `rawNode`
after `k` accepted `Ready`s, acknowledgements queued for `Advance` iff `adv` (`rawNode_at`).
`readyWithoutAccept` turns it into `readyFresh ... rd` (rd is the `Ready` of the current state; the
raft struct can be read, not changed: `readyFresh_ro`); anything stepped forgets freshness
(`readyFresh_forget`), keeping only the persistent `readyKept rn k rd`, from which R1's
`HasReady() = false` restores it (then `rd` is empty: `readyEmpty`). `ready_handout` hands a fresh
`Ready` out at the client's driver state (R1's `readyGot`), leaving `readyHanded`; `acceptReady`
moves to `rawNodeAt rn γ id (k+1) true`. `Advance`'s rendezvous (`rawNodeAt_advance`) takes what
R1's `Advance` takes (the driver after the batch was entered, the storage writes done, the view) and
gives R1's `Advance` post at once, leaving `rawNodeAdv` (`node.Advance` returns at the send, while
the run goroutine steps the acknowledgements: verify-round, A4 P3); `RawNode.Advance` opens it
(`rawNodeAdv_open`), releases each queued acknowledgement as an `ackOk` for `raft.Step`, and, given
back the struct and an `ackDone` for each, closes it to `rawNodeAt`. In between the struct is not
idle (`coreIdle`: its published floor is ahead of `applied`), so nothing but the acknowledgements
steps.

**Internal layer** (`raft.go`'s helpers; no client of raft uses it). `raftOpen r γ id o` is the
struct with its invariant opened, at `o : CoreOpen` (the view, R3's `LogState`, the read-only
queue's state, and the scalars the helpers move); `coreInv r γ id o` is the invariant's condition
at `o` (with the ghost state it owns). `raftCore_open`/`raftCore_close` move between them. A helper
that keeps the invariant takes and gives `coreInv` with its caller's check as a premise (`send`,
`becomeLeader`, `campaign`, `poll`, `sendMsgReadIndexResponse`, ...); a helper run with the
invariant broken (`reset`, `loadState`, `appliedSnap`) takes `raftOpen` alone and states its effect
on `o`; the result of a check is stated exactly over `o` (`promotable`, `hasUnappliedConfChanges`,
`committedEntryInCurrentTerm`, `pastElectionTimeout`), so its caller can pass the guard on
(`CampaignGuard`).

## Intended realization (raft's proof)

`raftCore r γ id ρ := ∃ o, ⌜o.view = ρ⌝ ∗ raftOpen r γ id o ∗ coreInv r γ id o`. `raftOpen` is the
struct's fields (Goose points-to; `id`, `logger`, `raftLog` persistent), the log (R3's `raftLog l
o.log` over the storage `logStorage l S snapValid γ.ns`), the tracker (R4's), the read-only queue
(R3's `readOnly`), the message queues (`msgs`, `msgsAfterAppend`, `readStates`,
`pendingReadIndexMessages`), and the ghost authorities of R1's node predicates for the `RawNode`
around `r` (driver, view, applied, storage-snapshot lower bounds, pending writes, running fraction:
ghost names attached to `r`, so that `raftOf rn r` reaches them). `raftRO` is a fraction of the
fields the getters read. `coreInv r γ id o` is the node's share of the cluster invariant (at
`γ.ns`, whose authorities are R1's), with these facts:

1. **Per-term leader logs** (ghost, monotone): the entries the leader of term `T` appended, those
   lost before they were written included (send-before-write, R1's `readyCheck`).
   `leaderOf γ T l` comes from a quorum of durable votes, one per voter and term (election safety,
   `leaderOf_agree`); each `MsgApp`/`MsgHeartbeat`/`MsgSnap`/`MsgTimeoutNow` fact is stated against
   the term's log (`msgSent_leaderOf`). The node's commit is a prefix of the committed log; its log
   matches every term log up to where it agrees (log matching), and a leader's log holds every entry
   committed before its term (leader completeness, by induction on terms). **After a crash**
   (R1's `raftState_crash`, the old state record kept with some of the batch's entries) a durable
   log may hold entries of a term `T'` above the durable term `T`; such a node cannot win an
   election at a term below `T'` (its candidacy quorums intersect the quorum that elected `T'`, whose
   members recorded a term at least `T'`, across at most one conf entry above its commit:
   `confAboveOk`), so `BatchOk`'s term clause stays true at the restart (verify-round, A4 P2(b)).
   A leader's own `Match`
   (`lastIndex` at `becomeLeader`) is durable-backed: its entries are in batches at or before the one
   carrying its self-vote, acknowledged only at `Advance`.
2. **Queued messages**: each with its protocol fact (`msgJust`), holding at the node's volatile
   state; the responses (`msgsAfterAppend`: vote and append responses) at the durable state once the
   batch carrying them is entered (R1's `readyEnter` mints their `msgSent`). An append acknowledgement
   at term `T` and index `i` means the sender's log matched the term-`T` log up to `i`, or the sender
   installed a replaced snapshot (R1's `msgSent_replaceSnap`: a prefix of the leader's delivered log,
   of a term at most the message's) when the term-`T` leader had left `T`, so that the response is
   stale where it lands (a heartbeat's commit is at most the agreement point; a delayed `MsgApp`
   below the commit returns before `maybeAppend`).
3. **Reads** (the old proof's scheme, `specs-ref/notes/raft-readindex-spec.md` §4.1): at the first
   step of a local `MsgReadIndex` (or of a forwarded one, at the leader), the read's persistent update
   (`readCtx`) is deposited in raft's invariant and fired at every ghost commit from then on; the
   leader answers at index `i` only when it registered the read at commit `i` with an entry of its
   term committed (`committedEntryInCurrentTerm`) and a quorum of its configuration acknowledged a
   heartbeat sent after the registration (or it is the only voter), so the deposit's commit is at
   most `i` and `i` at most the current commit: `readState γ c i` holds. The ghost commit steps one
   index at a time, firing the deposited read updates at each length, so "fired when the log was `i`
   long" exists for the leader's commit `i`; at registration the ghost commit equals the leader's,
   since the leader committed an entry of its term and the later quorum heartbeat excludes a newer
   leader (verify-round, A4 S4). A duplicate request (`γ.dup`)
   confirms the later registration (`readOnly.recvAck` keys by position); the commit only grows.
4. **Configurations** (R1's items 8-10; the provability review's V1-V3):
   - (V1) the view `⟨a, m⟩` (R1's `nodeConf`) is `confAt γ a m`, the tracker holds `m` (`o.conf = m`), and `a` is at
     least raft's applied index; it holds at `newRaft`, at `applyConfChange`, and after `appliedSnap`
     (where the view may move back to a client-chosen `a' ≥ s.index = applied`);
   - (V2) one pending change: if the node's log holds a conf entry `g` and the log of the leader
     that proposed `g` held a conf entry `f` before it, the node's commit is at least `f` (the leader
     proposed `g` after applying `f`, `pendingConfIndex`, so the `MsgApp` carrying `g` carried a commit
     of at least `f`; durable with the entries, R1's `wcommit`); in durable terms, every
     `raftState γ id D` has at most one conf entry above `D.wcommit` (a restart may present a commit
     as low as `wcommit`, `StorageHolds`; verify-round, A4 P2(b));
   - (V3) by V1, V2 and `hup`'s guard (`CampaignGuard`): when a leader first commits an index its view
     is `C_q` with `q` at least the last conf entry before the last conf entry in its log, and below
     the commit. So a candidate whose view is ahead of its log's end cannot win (every quorum of its
     view holds an entry past its log's end), and a node several configurations behind refuses to
     campaign; a candidate's quorums intersect every quorum that committed.
5. **Terms and indices** (the owner's protocol, `notes/bounds-plan.md`): the cluster invariant holds
   a time receipt `⧗` per term increase and per appended entry, deposited by `becomeCandidate` and
   `appendEntry` from their own Go steps, so every term is at most the receipts taken plus one (the
   bootstrap's term 1) and every index at most the receipts taken; the execution's bound
   (`receiptBound`, at most `2^63`, so that R3's `lastIndex < 2^63` premises hold too) enters at R1's
   `cluster_alloc` (requested in `req/go_etcd_io_raft_v3.md`; an open user decision, stated in
   `cluster_alloc.spec`'s docstring). The same bound is the intended source of **the sort bound**
   R4's specs take (`Visit`, `QuorumActive`, `VoterNodes`, `Committed`, `ConfState`,
   `CommittedIndex`: `GMap.size … ≤ Quorum.sortMax`, `2^62`): a committed configuration has at most
   the bootstrap peers plus one id per committed conf entry, each costing receipts (R4's question 2;
   the alternative, a bound in `Membership.Valid` with `changeV2` refusing past it, is R4's). Until
   then the sketches of `bcastAppend`, `bcastHeartbeatWithCtx`, `reset`, `maybeCommit`, `poll` that
   call those specs rest on it (integration I2).
6. **The `Ready` phases**: `readyFresh rn γ id k adv rd` is `rawNodeAt` with `rd` the `Ready` the
   current state gives (its slices raft's, until `ready_handout` moves them to the client);
   `readyKept rn k rd` keeps no claim on `rd`'s memory (`rd.Messages` aliases `r.msgs`, which a later
   `send` overwrites), only that `rd` was computed after `k` accepts. `HasReady() = false` after
   `readyKept rn k rd` restores freshness by monotonicity between two accepts: `msgs`,
   `msgsAfterAppend`, `readStates` and the log's next entries and committed entries only grow (R3),
   the hard state once different stays different (the term grows; a vote is reset only with a new
   term; the commit grows), and the soft state returns to the previous one only through a message of
   the term's leader, each of which queues a response. So a `Ready` computed after `k` accepts, at a
   state where `HasReady()` is later false, was empty (`readyEmpty`).

## Requirement snippets

`examples/specreq/raftcore/` (`//go:build ignore`, package `raft`): `step.go` (the sources of a
step, a forwarded proposal, a conf-change proposal, a transfer with its target; the only error;
ticks), `ready.go` (`node.run`'s `Ready` handling: computed, read, handed out, accepted, advanced;
`RawNode.Ready` twice; `NewRawNode`'s construction; `Bootstrap`), `conf.go` (`applyConfChange`),
`status.go` (the getters; `node.run`'s field reads; the logger).
-/
module

public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

/-! ## Pure -/

/-- **What a caller reads of the raft struct**: its hard state (`hardState()`: term, vote,
commit index), its leader and its role (`softState()`), and its progress map (`r.trk.Progress`:
peer id to `*Progress`; the ids of its configuration). -/
structure CoreView where
  hs : HardState
  lead : w64
  role : w64
  prs : GMap w64 Loc

/-- Where a stepped message comes from: outside raft.go's own `Ready` machinery, or an
acknowledgement of `RawNode` `rn`'s queue, released by `rawNodeAt_advance`. -/
inductive StepSrc where
  | outside
  | ack (rn : Loc)

/-- The local message types that need no resource: the timers' (`MsgHup`, `MsgBeat`,
`MsgCheckQuorum`) and the node API's reports (`ReportUnreachable`, `ReportSnapshot`,
`TransferLeader`, `ForgetLeader`, `Campaign`). -/
def isReportType (t : w32) : Bool :=
  decide (t ∈ [MsgHup, MsgBeat, MsgCheckQuorum, MsgUnreachable, MsgSnapStatus, MsgTransferLeader,
    MsgForgetLeader])

/-- The types of the acknowledgements `acceptReady` queues. -/
def ackTypes : List w32 :=
  [MsgAppResp, MsgVoteResp, MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp]

/-- `LocalAppendThread`, `LocalApplyThread`. -/
def localAppendThread : w64 := W64 (2 ^ 64 - 1)
def localApplyThread : w64 := W64 (2 ^ 64 - 2)

/-- `quorum.VoteWon`. -/
def voteWon : w8 := W8 3

/-- **`Config.validate`'s defaults**, with the logger `lg` it ends with: every other field kept. -/
def Config.defaulted [GooseExts] (cv : go_etcd_io.raft.v3.Config) (lg : GoInterface) :
    go_etcd_io.raft.v3.Config :=
  { cv with
    MaxUncommittedEntriesSize' := if cv.MaxUncommittedEntriesSize' = W64 0
      then W64 (2 ^ 64 - 1) else cv.MaxUncommittedEntriesSize',
    MaxCommittedSizePerReady' := if cv.MaxCommittedSizePerReady' = W64 0
      then cv.MaxSizePerMsg' else cv.MaxCommittedSizePerReady',
    MaxInflightBytes' := if cv.MaxInflightBytes' = W64 0
      then W64 (2 ^ 64 - 1) else cv.MaxInflightBytes',
    Logger' := lg }

/-- **An empty `Ready`**: no soft or hard state, read states, entries, snapshot, committed entries
or messages (what a `Ready` computed after an accept is when `HasReady()` is later false). -/
def readyEmpty [GooseExts] (rd : go_etcd_io.raft.v3.Ready) : Prop :=
  rd.SoftState' = null ∧ rd.HardState' = null ∧ rd.ReadStates'.len = W64 0 ∧
  rd.Entries'.len = W64 0 ∧ rd.Snapshot' = null ∧ rd.CommittedEntries'.len = W64 0 ∧
  rd.Messages'.len = W64 0 ∧ rd.MustSync' = false

/-! ### Internal: the opened struct -/

/-- (internal) **What `raft.go`'s helpers see of the opened struct**: the view, the log (R3's
`LogState`), the read-only queue (R3's `ReadOnlyState`), the tracker's configuration (`conf`:
integration I2, so that the invariant can say the tracker holds the view's configuration, the
realization's V1), `isLearner`, `leadTransferee`, `pendingConfIndex`, the election counters, and the
votes recorded (`trk.Votes`). -/
structure CoreOpen where
  view : CoreView
  conf : Membership
  log : LogState
  ro : ReadOnlyState
  isLearner : Bool
  leadTransferee : w64
  pendingConfIndex : w64
  electionElapsed : w64
  randomizedElectionTimeout : w64
  votes : GMap w64 Bool

/-- (internal) `hasUnappliedConfChanges()`: a conf entry committed and not applied. -/
def CoreOpen.unappliedConf (o : CoreOpen) : Prop :=
  ∃ e ∈ o.log.range (o.log.applied + 1) (o.log.committed + 1), e.isConfChange

/-- (internal) **`hup`'s guard**: the node `id` has a progress, is no learner, has no snapshot
pending, and no committed conf entry is unapplied. What `campaign` and `become(Pre)Candidate` take. -/
def CampaignGuard (id : w64) (o : CoreOpen) : Prop :=
  (o.view.prs !! id).isSome ∧ o.isLearner = false ∧ o.log.us.snap = none ∧ ¬ o.unappliedConf

/-- (internal) The heartbeat context the read-only queue gives (`readOnly.heartbeatCtx`). -/
def hbCtxOf (rs : ReadOnlyState) : List w8 :=
  if rs.pending = [] then [] else u64Le (W64 rs.position)

/-- (internal) **What `send` checks of a message** (`raft.go:514-601`): a vote request or response
carries a term, any other message none; a message that is not an append or vote response is not
addressed to the node itself. -/
def sendShape (id : w64) (m : Msg) : Prop :=
  (m.type ∈ [MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp] → m.term ≠ W64 0) ∧
  (m.type ∉ [MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp] → m.term = W64 0) ∧
  (m.type ∉ [MsgAppResp, MsgVoteResp, MsgPreVoteResp] → m.to ≠ id)

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## raftpb's and the tracker's Go ownership this batch uses

(Integration I2: were provisional opaques.) `entryPtrs sl dq es` is raftpb's (`RaftPb.entryPtrs`,
re-exported by `Api.lean`: a `[]*Entry` of any indices, a proposal's before `appendEntry` numbers
them). The tracker's are R4's (`tracker/Api.lean`), as below. -/

/-- The fresh memory of `getProgressCopy`'s map (part of R1's `statusOwn`): the map and each
`Progress` value, with its own `Inflights` clone (R4's `progressValOwn`). -/
def progressCopyOwn (mp : Loc) : IProp GF :=
  iprop(∃ (pm : GMap w64 go_etcd_io.raft.v3.tracker.Progress) (Ps : GMap w64 Tracker.ProgressV),
    ownMap mp (DFrac.own 1) pm ∗ [∗map] _id ↦ pv;P ∈ pm;Ps, Tracker.progressValOwn pv P)

/-- The result of confchange's `Changer` or `Restore` (R4's `resultOk` without its base): the
configuration `cfg` holds `m` and the progress map `trk` fits it (`Tracker.TrackerOk`). -/
def trkResult (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (m : Membership) :
    IProp GF :=
  iprop(Tracker.configOwn cfg (DFrac.own 1) m ∗
    ∃ prs pv, Tracker.progressMapOwn trk prs pv ∗ ⌜Tracker.TrackerOk m pv⌝)

/-! ## The raft struct -/

/-- **The raft struct `r` of node `id` of `γ`**, of which its callers read `ρ`. Exclusive. -/
opaque raftCore [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) : IProp GF := iprop(True)

/-- **A read-only share of the raft struct at view `ρ`**: what the getters and `node.run`'s field
reads take (`raftCore_ro`, `readyFresh_ro`). -/
opaque raftRO [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (id : w64) (ρ : CoreView) : IProp GF := iprop(True)

/-- `RawNode` `rn`'s raft struct is `r` (its `raft` field, never written after `NewRawNode`).
Persistent. -/
def raftOf (rn r : Loc) : IProp GF :=
  iprop(typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"raft" rn) r DFrac.discard)

/-- **A raft struct fresh from `newRaft`**, at view `ρ`, not yet in a `RawNode`: the node-level
start state (driver `st`, configuration view `v`, storage `S`, applied index `i`, storage snapshot
index `j`), one-shot (`raftBoot_bind`). -/
opaque raftBoot [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (γ : Cluster) (ρ : CoreView) (st : Driver) (v : ConfView)
    (S : StorState → IProp GF) (i j : Nat) : IProp GF := iprop(True)

/-- The fields of `r` that `node.run` and `node.Tick` read directly (`r.id`, `r.logger`: persistent;
`r.lead`, `r.Term`, `r.trk.Progress` at map `mp`, `r.tick`: the method value of `tickElection` or
`tickHeartbeat`). -/
def raftPeek (r : Loc) (id : w64) (ρ : CoreView) (mp : Loc) : IProp GF :=
  iprop(typedPointsto (structFieldRef go_etcd_io.raft.v3.raft go!"id" r) id DFrac.discard ∗
    (∃ lg : GoInterface,
      typedPointsto (structFieldRef go_etcd_io.raft.v3.raft go!"logger" r) lg DFrac.discard ∗
      loggerOk lg) ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.raft go!"lead" r) ρ.lead (DFrac.own 1) ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.raft go!"Term" r) ρ.hs.term (DFrac.own 1) ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.tracker.ProgressTracker go!"Progress"
      (structFieldRef go_etcd_io.raft.v3.raft go!"trk" r)) mp (DFrac.own 1) ∗
    ownMap mp (DFrac.own 1) ρ.prs ∗
    ∃ f : GoFunc, typedPointsto (structFieldRef go_etcd_io.raft.v3.raft go!"tick" r) f (DFrac.own 1) ∗
      ⌜f = methods (go.GoType.PointerType go_etcd_io.raft.v3.raft.ty) go!"tickElection" #r ∨
       f = methods (go.GoType.PointerType go_etcd_io.raft.v3.raft.ty) go!"tickHeartbeat" #r⌝)

/-! ## The provenance of a stepped message -/

/-- **The update a client hands raft with a proposed entry `e`** (`node.Propose`'s,
`node.ProposeConfChange`'s, with the entry's type and bytes): fired when the entry commits, at the
term `t` it was appended in; persistent when `γ.dup`. -/
def propUpd (γ : Cluster) (e : LogEntry) : IProp GF :=
  iprop(□?γ.dup AU <{ ∃∃ (ops : List LogEntry), committedOps γ ops }> @ ⊤ \ ↑γ.ns, ∅
    <{ ∀∀ (t : w64), committedOps γ (ops ++ opsOf [{ e with term := t }]), COMM True }>)

/-- **A message stepped from outside the `Ready` machinery**:
- received from a node of `γ`, addressed to `id`, with its credit; a proposal's sender may since have
  been rewritten (`node.run` sets `From` to the node's id before stepping a proposal from `propc`,
  `node.go:388`: the leader never reads a proposal's sender, a follower forwards it with its own);
- a local proposal (unstamped, from no one or `id`), each entry with its client's update or raft's
  own (a filler, the auto-leave entry), its conf-change entries decoding;
- a local read (unstamped, one entry: the registered context);
- a local timer or report message (unstamped). -/
def stepIn (γ : Cluster) (id : w64) (m : Msg) : IProp GF :=
  iprop((∃ s : w64, ⌜s = m.src ∨ m.type = MsgProp⌝ ∗ msgSent γ { m with src := s } ∗
      msgCredit γ { m with src := s } ∗ ⌜m.to = id⌝) ∨
    (⌜m.type = MsgProp ∧ m.term = W64 0 ∧ (m.src = W64 0 ∨ m.src = id) ∧ m.entries ≠ [] ∧
        ∀ e ∈ m.entries, e.isConfChange → (decodeConfChange e.type e.data).isSome⌝ ∗
      [∗list] e ∈ m.entries, ⌜e.isFiller ∨ e.isEmptyV2⌝ ∨ propUpd γ e) ∨
    (∃ (e : LogEntry) (Q : List LogEntry → IProp GF),
      ⌜m.type = MsgReadIndex ∧ m.term = W64 0 ∧ (m.src = W64 0 ∨ m.src = id) ∧
        m.entries = [e]⌝ ∗ readCtx γ e.data Q) ∨
    ⌜m.term = W64 0 ∧ isReportType m.type = true⌝)

/-- **The raft struct `r` is idle**: no acknowledgement released by `Advance` is being stepped, so
its published floor (R3's `floor`) is at most its applied index (`coreIdle_floor`). Exclusive. Held
in `rawNodeAt` (`rawNodeAt_core` lends it with the struct); `rawNodeAt_advance` takes it while the
acknowledgements step (R3's floor is then published at the delivered log, ahead of `applied`, so a
`MsgHup`'s scan of `(applied, committed]` could meet a compaction: `hasUnappliedConfChanges` panics
on it), and its closing gives it back. A step from outside (`stepIn`: a tick, a campaign, any
received message) and the helpers that may campaign (`hup`, the ticks) take it. (Verify-round, A4
P3.) -/
opaque coreIdle [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) : IProp GF := iprop(True)

/-- **An acknowledgement of `RawNode` `rn`'s queue, released for stepping** (`rawNodeAt_advance`:
the batch it acknowledges was entered and written). Exclusive: stepped once. The struct's
idle token (`coreIdle`) stays in `rawNodeAdv` and comes back at `rawNodeAdv_open`'s closing; when
the batch has an apply acknowledgement, that acknowledgement's `ackOk` lends it (`appliedTo`'s
auto-leave proposal, once `applied` reaches the published floor) and its `ackDone` returns it. A
batch with no committed entries, or with a snapshot (acknowledged by `appliedSnap`, at a
non-leader), has no apply acknowledgement and does not need it. (Re-review S-b.) -/
opaque ackOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (m : Msg) : IProp GF := iprop(True)

/-- The receipt that acknowledgement `m` was stepped (`raft.Step`'s post), which
`rawNodeAt_advance`'s closing takes. -/
opaque ackDone [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (m : Msg) : IProp GF := iprop(True)

/-- **The message `raft.Step` takes** (`ml`, holding `m`): a received message (`msgRecv`: its
`Entries` slice's capacity owned, which `handleAppendEntries` hands to the log, whose `unstable`
may adopt the slice), or an owned message that is no `MsgApp` (raft's own: local proposals, reads,
reports, acknowledgements). (Integration I2, the coordinator's decision on the `MsgApp` capacity.) -/
def stepMsg (ml : Loc) (m : Msg) : IProp GF :=
  iprop(msgRecv ml m ∨ (msgPts ml (DFrac.own 1) m ∗ ⌜m.type ≠ MsgApp⌝))

/-- `raft.Step`'s precondition by source (`r` the raft struct): from outside, the message's
provenance and the struct's idle token (no acknowledgement being stepped: `coreIdle`). -/
def stepPre (r : Loc) (γ : Cluster) (id : w64) (m : Msg) : StepSrc → IProp GF
  | .outside => iprop(stepIn γ id m ∗ coreIdle r)
  | .ack rn => iprop(raftOf rn r ∗ ackOk rn γ m)

/-- `raft.Step`'s postcondition by source. -/
def stepPost (r : Loc) (γ : Cluster) (m : Msg) : StepSrc → IProp GF
  | .outside => coreIdle r
  | .ack rn => ackDone rn γ m

/-! ## The `RawNode`'s `Ready` phases (`rawnode.go`'s internals) -/

/-- **R1's `rawNode rn γ id` after `k` accepted `Ready`s**, with acknowledgements queued for
`Advance` iff `adv` (`rawNode_at`). Exclusive. -/
opaque rawNodeAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) : IProp GF :=
  iprop(True)

/-- **`rawNodeAt rn γ id k adv`, with `rd` the `Ready` of its current state** (computed by
`readyWithoutAccept`, nothing stepped since). Exclusive. -/
opaque readyFresh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool)
    (rd : go_etcd_io.raft.v3.Ready) : IProp GF := iprop(True)

/-- `rd` was computed by `readyWithoutAccept` after `k` accepted `Ready`s (no claim on its memory).
Persistent. -/
opaque readyKept [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (k : Nat) (rd : go_etcd_io.raft.v3.Ready) : IProp GF := iprop(True)

/-- **`Ready` `rd` handed out** (`ready_handout`), its `acceptReady` due. Exclusive. -/
opaque readyHanded [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (rd : go_etcd_io.raft.v3.Ready) :
    IProp GF := iprop(True)

/-- **`RawNode` `rn` between `Advance`'s rendezvous and its acknowledgements**: the client's half
of `Advance` handed out (`rawNodeAt_advance`), the acknowledgements still to step
(`rawNodeAdv_open`); what `RawNode.Advance` takes. Exclusive. (Verify-round, A4 P3.) -/
opaque rawNodeAdv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) : IProp GF :=
  iprop(True)

/-! ## Internal: the opened struct and cluster facts `raft.go`'s helpers use

No client of raft sees these (to be listed internal in `etc/api` when raft's API list is made). -/

/-- (internal) **The raft struct with its invariant opened**, at `o`. Exclusive. -/
opaque raftOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) : IProp GF := iprop(True)

/-- (internal) **The invariant's condition at `o`** (`ApiCore.lean`'s realization, items 1-5), with
the ghost state it owns. -/
opaque coreInv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) : IProp GF := iprop(True)

/-- (internal) The invariant's condition at `o` once the tracker is at membership `m`
(`switchToConfig`'s leader branch). -/
opaque coreInvConf [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (m : Membership) : IProp GF :=
  iprop(True)

/-- (internal) **The opened struct with its tracker taken out** (`raftOpen_trk`): put any tracker
back (R4's `progressTracker`) and it is the opened struct at that tracker's configuration, map and
votes. `switchToConfig` takes it with the old tracker's shell (`trkShell`), after confchange's
`Changer` consumed the old progress map (`applyConfChange`) or while `Restore` built a new one on a
fresh tracker (`appliedSnap`, `newRaft`). (Integration I2.) -/
def raftTrkOpen (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) : IProp GF :=
  iprop(∀ T : Tracker.TrackerV, Tracker.progressTracker (structFieldRef go_etcd_io.raft.v3.raft go!"trk" r) T -∗
    raftOpen r γ id { o with conf := T.conf, view := { o.view with prs := T.prs }, votes := T.votes })

/-- (internal) **The tracker's shell**: the `ProgressTracker` struct at `t` (its `Config` and
`Progress` about to be replaced), its votes and ring capacities. -/
def trkShell (t : Loc) (votes : GMap w64 Bool) (mi mb : w64) : IProp GF :=
  iprop(∃ tv : go_etcd_io.raft.v3.tracker.ProgressTracker, typedPointsto t tv (DFrac.own 1) ∗
    ownMap tv.Votes' (DFrac.own 1) votes ∗ ⌜tv.MaxInflight' = mi ∧ tv.MaxInflightBytes' = mb⌝)

/-- (internal) **Message `m`'s protocol fact holds at the node's current state**: what `send` queues
it with (its `msgSent` minted when the batch carrying it is handed out or entered). Exclusive. -/
opaque msgJust [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (γ : Cluster) (id : w64) (m : Msg) : IProp GF := iprop(True)

/-- (internal) **A vote from `src` of type `t` (granted iff `v`) for node `id` at term `T`**: a
`msgSent` vote response (`msgSent_voteFrom`), or the node's own acknowledged vote. Persistent. -/
opaque voteFrom [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (id : w64) (T : w64) (t : w32) (src : w64) (v : Bool) : IProp GF :=
  iprop(True)

/-- (internal) **A read confirmed at index `i`** (the request message `m`, registered at a leader of
its term with an entry of the term committed, acknowledged by a quorum): its update fired at `i`.
Persistent. -/
opaque readConfirmed [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (m : Msg) (i : w64) : IProp GF := iprop(True)

/-- (internal) **`l` won the election of term `t`**. Persistent. -/
opaque leaderOf [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (t : w64) (l : w64) : IProp GF := iprop(True)

/-! ## The package's loggers (`logger.go`) -/

/-- **`l` is a `*DefaultLogger`** over a valid `*log.Logger`, its fields frozen. Persistent. -/
opaque defaultLoggerOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) : IProp GF := iprop(True)

/-- **A `*DefaultLogger` not yet shared** (its `debug` flag and its `log.Logger`'s flags writable).
Exclusive. -/
opaque defaultLoggerOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) : IProp GF := iprop(True)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

def core_persistent.spec : Prop :=
  (∀ rn k rd, Persistent (readyKept (GF := GF) rn k rd)) ∧
  (∀ γ t l, Persistent (leaderOf (GF := GF) γ t l)) ∧
  (∀ γ id T t s v, Persistent (voteFrom (GF := GF) γ id T t s v)) ∧
  (∀ γ m i, Persistent (readConfirmed (GF := GF) γ m i)) ∧
  (∀ l, Persistent (defaultLoggerOk (GF := GF) l))

def raftCore_exclusive.spec : Prop :=
  ∀ r γ id ρ γ' id' ρ', raftCore (GF := GF) r γ id ρ ∗ raftCore r γ' id' ρ' ⊢ iprop(False)

/-- **A read-only share** of the raft struct: given back at the same view. -/
def raftCore_ro.spec : Prop :=
  ∀ r γ id ρ, raftCore (GF := GF) r γ id ρ ⊢ raftRO r id ρ ∗ (raftRO r id ρ -∗ raftCore r γ id ρ)

/-- **The fields `node.run` reads** (`r.lead`, `r.Term`, `r.id`, `r.logger`, `r.trk.Progress`,
`r.tick`), given back unchanged. -/
def raftRO_peek.spec : Prop :=
  ∀ r id ρ, raftRO (GF := GF) r id ρ ⊢
    ∃ mp, raftPeek r id ρ mp ∗ (raftPeek r id ρ mp -∗ raftRO r id ρ)

/-- **Binding a fresh raft struct to its `RawNode`** (`NewRawNode`): with the `RawNode`'s fields
as `NewRawNode` sets them, the `RawNode`'s token and R1's node predicates keyed by it. -/
def raftBoot_bind.spec : Prop :=
  ∀ (rn r : Loc) γ id (ρ : CoreView) st v (S : StorState → IProp GF) (i j : Nat)
    (ps ph : Loc) (sl : GoSlice),
    raftBoot (GF := GF) r γ ρ st v S i j ∗ raftCore r γ id ρ ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"raft" rn) r (DFrac.own 1) ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"asyncStorageWrites" rn) false
      (DFrac.own 1) ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"prevSoftSt" rn) ps (DFrac.own 1) ∗
    typedPointsto ps (go_etcd_io.raft.v3.SoftState.mk ρ.lead ρ.role) (DFrac.own 1) ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"prevHardSt" rn) ph (DFrac.own 1) ∗
    hardStatePts ph (DFrac.own 1) ρ.hs ∗
    typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"stepsOnAdvance" rn) sl
      (DFrac.own 1) ∗ ⌜sl = slice.nil⌝ ⊢ |==>
      rawNodeAt rn γ id 0 false ∗ nodeDriver rn γ st ∗ nodeConf rn γ v ∗ nodeStorage rn γ S ∗
      appliedLb rn i ∗ storSnapLb rn j ∗ nodeRunning rn 1

/-- **R1's `RawNode` token is `rawNodeAt` at some phase.** -/
def rawNode_at.spec : Prop :=
  ∀ rn γ id, rawNode (GF := GF) rn γ id ⊣⊢ ∃ k adv, rawNodeAt rn γ id k adv

/-- **The raft struct of a `RawNode`**: open to call its methods (with its idle token: no
acknowledgement is being stepped); closed again at any view (a step does not change the phase). -/
def rawNodeAt_core.spec : Prop :=
  ∀ rn γ id k adv, rawNodeAt (GF := GF) rn γ id k adv ⊢
    ∃ r ρ, raftOf rn r ∗ raftCore r γ id ρ ∗ coreIdle r ∗
      (∀ ρ', raftCore r γ id ρ' -∗ coreIdle r -∗ rawNodeAt rn γ id k adv)

/-- **`Advance`'s rendezvous** (`rawnode.go:477-490`; `node.Advance`'s send on `advancec`): with
what R1's `Advance` takes (the driver after the batch was entered, the storage writes done, the view,
and the conf entries past it decided skip when no snapshot came), R1's `Advance` post **at once**:
the driver's snapshot done, the applied index at the delivered log, the view kept or (after a
snapshot) any committed configuration point at or after the snapshot's index the client chooses;
the `RawNode` is left with its acknowledgements to step (`rawNodeAdv`). (Verify-round, A4 P3: the
post was given at the closing, after the steps, which `node.Advance` -- returning at the send,
while the run goroutine steps them concurrently -- cannot wait for.)
Realization against R3's log laws: the batch is folded into the log (`raftLog_absorb`: R1's
`readyStor rn none j []` is R3's `logPending h false false`), and the delivered log is published as
a floor (`raftLog_publish` at `i ≤ applying`, the batch absorbed: each delivered entry was written
in this batch or an earlier one and is committed, so frozen; for a batch with a snapshot, whose
delivered log ends at `s.index` while `applying` has not moved, the floor is the one
`logStor_install` gave, `logFloor l s.index s.term`, which `readyStor rn none j []` keeps for raft's
side: re-review S-a), which is R1's `appliedLb`
(`logFloor_agree` ties its term to the committed log); the struct's idle token is taken
(`coreIdle`: its floor is ahead of `applied` until the apply acknowledgement is stepped). The view's
ghost may move to the snapshot's configuration before the tracker does (`appliedSnap`, stepped
next): the realization's V1 holds the view at the tracker's configuration or, with an unstepped
snapshot acknowledgement, at a point at or after its index (no `ApplyConfChange` reaches the
struct before the steps end: `node.run` is sequential). -/
def rawNodeAt_advance.spec : Prop :=
  ∀ rn γ id k adv (st : Driver) (j : Nat) (v : ConfView),
    rawNodeAt (GF := GF) rn γ id k adv ∗ nodeDriver rn γ st ∗ readyStor rn none j [] ∗
      nodeConf rn γ v ∗
      (match st.lastSnap with
       | none => confSkipped γ st.delivered v.applied st.delivered.length
       | some _ => iprop(True)) ⊢ |==>
    rawNodeAdv rn γ id k adv ∗ nodeDriver rn γ { st with lastSnap := none } ∗
    appliedLb rn st.delivered.length ∗
    match st.lastSnap with
    | none => nodeConf rn γ v
    | some s => (∀ a m, confAt γ a m -∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is m⌝ -∗
        |={⊤}=> nodeConf rn γ ⟨a, m⟩)

/-- **The acknowledgements to step** (`RawNode.Advance`'s body): the raft struct and the queued
acknowledgements (each released, `ackOk`; none unless `adv`); given back the struct (any view), the
field at an emptied slice of the same array and an `ackDone` for each, the `RawNode` with nothing
queued (its idle token back: the apply acknowledgement moved `applied` to the published floor). -/
def rawNodeAdv_open.spec : Prop :=
  ∀ rn γ id k adv, rawNodeAdv (GF := GF) rn γ id k adv ⊢
    ∃ (r : Loc) (ρ : CoreView) (sl : GoSlice) (ps : List Loc) (ms : List Msg),
      raftOf rn r ∗ raftCore r γ id ρ ∗
      typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"stepsOnAdvance" rn) sl
        (DFrac.own 1) ∗
      ownSlice sl ps (DFrac.own 1) ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
      ⌜ps.length = ms.length ∧ (adv = false → ms = [])⌝ ∗
      ([∗list] pm ∈ ps.zip ms, msgPts pm.1 (DFrac.own 1) pm.2 ∗ ackOk rn γ pm.2) ∗
      (∀ (ρ' : CoreView) (sl' : GoSlice) (ps' : List Loc),
        raftCore r γ id ρ' ∗
        typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"stepsOnAdvance" rn) sl'
          (DFrac.own 1) ∗ ownSlice sl' ps' (DFrac.own 1) ∗ ownSliceCap Loc sl' (DFrac.own 1) ∗
          ⌜ps' = []⌝ ∗ ([∗list] m ∈ ms, ackDone rn γ m) ={⊤}=∗
        rawNodeAt rn γ id k false)

/-- The acknowledgements are responses, never proposals. -/
def ackOk_type.spec : Prop :=
  ∀ rn γ (m : Msg), ackOk (GF := GF) rn γ m ⊢ iprop(⌜m.type ∈ ackTypes⌝)

/-- A fresh `Ready` stops being fresh when anything is stepped: what remains is the token and the
persistent record that it was computed in this phase. -/
def readyFresh_forget.spec : Prop :=
  ∀ rn γ id k adv rd, readyFresh (GF := GF) rn γ id k adv rd ⊢
    rawNodeAt rn γ id k adv ∗ readyKept rn k rd

/-- **Reads while a `Ready` is fresh** (`node.run`'s field reads and `hasLeader` between computing a
`Ready` and sending it, `node.go:367-380`): a read-only share of the struct, given back at the same
view. -/
def readyFresh_ro.spec : Prop :=
  ∀ rn γ id k adv rd, readyFresh (GF := GF) rn γ id k adv rd ⊢
    ∃ r ρ, raftOf rn r ∗ raftRO r id ρ ∗ (raftRO r id ρ -∗ readyFresh rn γ id k adv rd)

/-- **Handing a `Ready` out** (`node.run`'s send on `readyc`, inside the receive's update;
`RawNode.Ready`): a fresh `Ready` computed with no acknowledgement pending, at the client's driver
state, gives R1's `readyGot` and leaves its `acceptReady` due. -/
def ready_handout.spec : Prop :=
  ∀ rn γ id k rd (st : Driver),
    readyFresh (GF := GF) rn γ id k false rd ∗ nodeDriver rn γ st ⊢ |==>
      readyHanded rn γ id k rd ∗ readyGot rn γ id st rd

/-- **`RawNode.Bootstrap`'s window** (`bootstrap.go:32-81`): a `RawNode` started on an empty storage
(driver at the empty start) opens to the struct at the empty log and hard state, with its log field,
the `RawNode`'s `prevHardSt` and the bootstrap log committed; after `becomeFollower(1, None)`, the
bootstrap entries appended and committed (R3's `raftLog`, through `raftOpen_log`) and `prevHardSt`
set to the empty hard state, it closes to the struct, on which `applyConfChange` applies each
bootstrap change (decided at `cluster_alloc`), and then to the token. -/
def rawNodeAt_bootstrap.spec : Prop :=
  ∀ rn γ id k adv (boot : List LogEntry),
    rawNodeAt (GF := GF) rn γ id k adv ∗ nodeDriver rn γ (Driver.start [] HardState.empty Durable.init) ∗
      bootLog γ boot ⊢
    ∃ (r : Loc) (o : CoreOpen) (ph : Loc),
      raftOf rn r ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ committedLb γ boot ∗
      ⌜o.view.hs = HardState.empty ∧ o.log.lastIndex = 0 ∧ o.log.committed = 0⌝ ∗
      typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"prevHardSt" rn) ph (DFrac.own 1) ∗
      (∀ (o' : CoreOpen) (ph' : Loc),
        raftOpen r γ id o' ∗
        typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"prevHardSt" rn) ph'
          (DFrac.own 1) ∗ hsPtr ph' DFrac.discard HardState.empty ∗
        ⌜o'.view.hs.term = W64 1 ∧ o'.view.role = StateFollower ∧ o'.log.log = boot ∧
          o'.log.committed = boot.length⌝ ={⊤}=∗
        raftCore r γ id o'.view ∗
        (∀ ρ', raftCore r γ id ρ' -∗ rawNodeAt rn γ id k adv) ∗
        nodeDriver rn γ (Driver.start [] HardState.empty Durable.init))

/-! ### Internal -/

/-- (internal) **Opening the struct**: its invariant's condition at its state. -/
def raftCore_open.spec : Prop :=
  ∀ r γ id ρ, raftCore (GF := GF) r γ id ρ ⊢
    ∃ o, ⌜o.view = ρ⌝ ∗ raftOpen r γ id o ∗ coreInv r γ id o

/-- (internal) **Closing it** where the invariant's condition holds. -/
def raftCore_close.spec : Prop :=
  ∀ r γ id o, raftOpen (GF := GF) r γ id o ∗ coreInv r γ id o ⊢ raftCore r γ id o.view

/-- (internal) The log (R3's `raftLog`) of the opened struct, through its `raftLog` field. -/
def raftOpen_log.spec : Prop :=
  ∀ r γ id o, raftOpen (GF := GF) r γ id o ⊢
    ∃ l : Loc, typedPointsto (structFieldRef go_etcd_io.raft.v3.raft go!"raftLog" r) l DFrac.discard ∗
      raftLog l o.log ∗ (∀ ls', raftLog l ls' -∗ raftOpen r γ id { o with log := ls' })

/-- (internal) **The tracker** (R4's `progressTracker`) of the opened struct, through its `trk`
field: at the open state's configuration, map and votes; closed again by any tracker
(`raftTrkOpen`). What the helpers that read or move the tracker use (`reset`, `poll`, the send
helpers' `Progress` updates, `applyConfChange`'s `Changer`, `switchToConfig`). (Integration I2: the
sketches used R4's tracker specs with no way to reach the tracker.) -/
def raftOpen_trk.spec : Prop :=
  ∀ r γ id o, raftOpen (GF := GF) r γ id o ⊢
    ∃ T : Tracker.TrackerV, Tracker.progressTracker (structFieldRef go_etcd_io.raft.v3.raft go!"trk" r) T ∗
      ⌜T.conf = o.conf ∧ T.prs = o.view.prs ∧ T.votes = o.votes⌝ ∗ raftTrkOpen r γ id o

/-- (internal) **An idle struct's floor is at most its applied index** (what `hup`'s
`hasUnappliedConfChanges` scan needs: no compaction above `applied`). -/
def coreIdle_floor.spec : Prop :=
  ∀ r γ id o, raftOpen (GF := GF) r γ id o ∗ coreInv r γ id o ∗ coreIdle r ⊢
    raftOpen r γ id o ∗ coreInv r γ id o ∗ coreIdle r ∗ ⌜o.log.floor ≤ o.log.applied⌝

/-- (internal) A read-only share of an opened struct. -/
def raftOpen_ro.spec : Prop :=
  ∀ r γ id o, raftOpen (GF := GF) r γ id o ⊢
    raftRO r id o.view ∗ (raftRO r id o.view -∗ raftOpen r γ id o)

/-- **Election safety**: a term has at most one leader. -/
def leaderOf_agree.spec : Prop :=
  ∀ γ t (l1 l2 : w64), leaderOf (GF := GF) γ t l1 ∗ leaderOf γ t l2 ⊢ iprop(⌜l1 = l2⌝)

/-- (internal) Only the leader of a term sends appends, heartbeats, snapshots and `MsgTimeoutNow`
in it. -/
def msgSent_leaderOf.spec : Prop :=
  ∀ γ (m : Msg), m.type ∈ [MsgApp, MsgHeartbeat, MsgSnap, MsgTimeoutNow] →
    msgSent (GF := GF) γ m ⊢ leaderOf γ m.term m.src

/-- (internal) A sent vote response is a vote for its receiver at its term. -/
def msgSent_voteFrom.spec : Prop :=
  ∀ γ (m : Msg), m.type = MsgVoteResp ∨ m.type = MsgPreVoteResp →
    msgSent (GF := GF) γ m ⊢ voteFrom γ m.to m.term m.type m.src (!m.reject)

/-! ### Loggers and the package's variables -/

/-- **A logger meeting raft's contract is not `nil`.** (R1's `loggerOk`.) -/
def loggerOk_nonnil.spec : Prop :=
  ∀ lg, loggerOk (GF := GF) lg ⊢ iprop(⌜lg ≠ interface.nil⌝)

/-- A `*DefaultLogger` meets raft's `Logger` contract. -/
def defaultLogger_loggerOk.spec : Prop :=
  ∀ l, defaultLoggerOk (GF := GF) l ⊢
    loggerOk (interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.DefaultLogger.ty) #l)

def defaultLoggerOwn_share.spec : Prop :=
  ∀ l, defaultLoggerOwn (GF := GF) l ⊢ |==> defaultLoggerOk l

/-- **The package's initialized variables** raft's specs read (verify-round, A4 P5: the lock
invariants and the read-only tables were promised but missing): the two default loggers;
`raftLoggerMu`'s lock invariant (the package logger `raftLogger` meets `loggerOk`: `getLogger`,
`SetLogger`, `ResetDefaultLogger`, `Config.validate` with a `nil` logger); the random source
`globalRand` and its mutex (invariant `True`: `lockedRand.Intn`); `emptyState`, the empty hard state
(`IsEmptyHardState`, `acceptReady`, `RawNode.Bootstrap`); `stmap`, the four role names
(`StateType.String`); `errBreak`, a non-`nil` error (`hasUnappliedConfChanges` compares the scan's
error with it: both loads give this value); the `isLocalMsg`/`isResponseMsg` tables
(`IsLocalMsg`, `IsResponseMsg`: entry `t` is `isLocalMsgType t`, `isResponseMsgType t`). Each is
read-only after initialization, so the whole is persistent. -/
def raft_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ⊢
    ∃ (l1 l2 lr pe : Loc) (eb : GoInterface) (names : List GoString) (bl br : List Bool),
      typedPointsto (globalAddr go_etcd_io.raft.v3.defaultLogger) l1 DFrac.discard ∗
      defaultLoggerOk l1 ∗
      typedPointsto (globalAddr go_etcd_io.raft.v3.discardLogger) l2 DFrac.discard ∗
      defaultLoggerOk l2 ∗
      sync.isMutex (globalAddr go_etcd_io.raft.v3.raftLoggerMu)
        iprop(∃ lg : GoInterface,
          typedPointsto (globalAddr go_etcd_io.raft.v3.raftLogger) lg (DFrac.own 1) ∗ loggerOk lg) ∗
      typedPointsto (globalAddr go_etcd_io.raft.v3.globalRand) lr DFrac.discard ∗
      sync.isMutex (structFieldRef go_etcd_io.raft.v3.lockedRand go!"mu" lr) iprop(True) ∗
      typedPointsto (globalAddr go_etcd_io.raft.v3.emptyState) pe DFrac.discard ∗
      hardStatePts pe DFrac.discard HardState.empty ∗
      typedPointsto (globalAddr go_etcd_io.raft.v3.stmap) (⟨names⟩ : GoArray GoString 4)
        DFrac.discard ∗ ⌜names.length = 4⌝ ∗
      errIs go_etcd_io.raft.v3.errBreak eb ∗ ⌜eb ≠ interface.nil⌝ ∗
      typedPointsto (globalAddr go_etcd_io.raft.v3.isLocalMsg) (⟨bl⟩ : GoArray Bool 23)
        DFrac.discard ∗
      typedPointsto (globalAddr go_etcd_io.raft.v3.isResponseMsg) (⟨br⟩ : GoArray Bool 23)
        DFrac.discard ∗
      ⌜bl.length = 23 ∧ br.length = 23 ∧
        ∀ t : w32, 0 ≤ sint.Z t →
          (bl[uint.nat t]?).getD false = isLocalMsgType t ∧
          (br[uint.nat t]?).getD false = isResponseMsgType t⌝

end laws

end Raft
end EtcdGrove
end Perennial
