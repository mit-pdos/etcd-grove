/-
# Raft's core (batch R2): the vocabulary of the `raft` struct

What the node API (R1: `Api.lean`, `Model.lean`; `RawNode`'s and `node`'s proofs) uses of the raft
state machine in `raft.go`: one exclusive token for the raft struct, the provenance of a message it
steps, and the `RawNode`-level phases of a `Ready` (computed, handed out, accepted, its
acknowledgements stepped at `Advance`). The specs of the functions are the files beside it
(`newRaft.lean`, `raft__Step.lean`, `RawNode__acceptReady.lean`, ...).

## The shape, in words

**The raft struct** `r` of node `id` of cluster `γ` is `raftCore r γ id ρ`: exclusive, created by
`newRaft`, held inside the `RawNode` around it (`rawNode`, R1's token). `ρ : CoreView` is only what
its callers read of it with Go field reads or getters: the hard state (term, vote, commit), the
leader, the role and the progress map's entries. Everything else (the log, the tracker, the
read-only queue, the queued messages, the protocol's ghost state) is inside the token, and
**`raft.Step` keeps the token for every message, every state and every feature** (PreVote,
CheckQuorum, learners, leader transfer, joint consensus, snapshots): its precondition is only the
message's provenance (`stepIn`: received with its `msgSent` and credit; a local proposal with its
client's updates; a local read with its registered context; a local report or timer message; or an
acknowledgement `acceptReady` queued, `ackOk`), and its post says only what callers inspect (the
error is `ErrProposalDropped` for a dropped `MsgProp`, `nil` otherwise). The protocol's safety is
not stated per step: it is the meaning of R1's cluster vocabulary (`committedLb`, `confAt`,
`readState`, `msgSent`, `raftState`), which `raft.Step` keeps true, and of the `Ready` raft hands
out (R1's `readyGot`).

**Binding to a `RawNode`.** `newRaft` cannot know the `RawNode` it will be in (`NewRawNode`
allocates it after). It returns the node-level start state as a one-shot `raftBoot r ...`; once the
`RawNode` `rn` holds `r` in its `raft` field (`raftOf rn r`, persistent), `raftBoot_bind` turns it
into R1's node predicates keyed by `rn` (`nodeDriver rn`, `nodeConf rn`, ...) and into the
`RawNode`'s token `rawNodeAt rn γ id 0 false`. The raft struct's methods that move node-level state
(`applyConfChange`, the acknowledgements `Advance` steps) take R1's predicates keyed by the
`RawNode` `rn` with `raftOf rn r`.

**The `Ready` phases** (`rawnode.go`, internal; R1 left them to this batch). `rawNodeAt rn γ id k adv`
is R1's `rawNode rn γ id` after `k` accepted `Ready`s, with `adv` saying whether acknowledgements
are queued for `Advance` (`rawNode_at`). `readyWithoutAccept` turns it into `readyFresh ... rd` (rd is
the `Ready` of the current state); any change of the raft state forgets that (`readyFresh_forget`),
keeping only the persistent `readyKept rn k rd`, from which `HasReady() = false` restores
freshness (R1's `HasReady`; `node.run` may send a `Ready` computed before other steps).
`ready_handout` hands a fresh `Ready` out at the client's driver state (R1's `readyGot`: the batch,
its facts and updates), leaving `readyHanded`; `acceptReady` then moves to `rawNodeAt rn γ id (k+1)
true`, its acknowledgements queued in the `RawNode` (`rawNodeAt_advance`), each an `ackOk` that
`raft.Step` takes with the evidence that the batch was entered and written.

## Intended realization (raft's proof)

- `raftCore r γ id ρ`: the struct's fields (Goose points-to; `id` and `logger` persistent), the log
  (R3's `raftLog`/`unstable` predicates, over the storage contents `S σ` that R1's node invariant
  holds), the tracker (R4's), the read-only queue (R3's), and the node's protocol state: its term
  and vote (at least the durable ones: the client's `raftState γ id D` and its authority half in the
  cluster invariant at `γ.ns`), its log (the durable log of the batches handed out, then the
  unstable entries), its commit index (a prefix of the cluster's committed log: `committedLb`), its
  tracker's configuration (R1's `nodeConf` view: `confAt γ applied`), the votes received in its term
  (each a `msgSent` vote response), and, for each queued message, its justification: the protocol
  fact its `msgSent` will record (the sender's term, its log up to the index sent, its vote, its
  commit knowledge, the leader's term for `MsgApp`/`MsgHeartbeat`/`MsgSnap`), holding at the node's
  volatile state, and at its durable state once the batch carrying it is entered (vote and append
  responses: `msgsAfterAppend`). The deposited proposal updates ride in the leader's log (fired when
  its commit index covers them), the confirmed reads' updates in the read-only queue (fired when a
  quorum of the current configuration acknowledges a heartbeat sent after the read was registered,
  at a leader that has committed an entry of its term). The authorities of R1's node predicates for
  the `RawNode` around `r` (the driver's delivered log, durable state and last hard state; the
  configuration view; the applied and storage-snapshot lower bounds; the pending storage writes;
  the running fraction) are ghost state named from `r` (Iris `meta`, or a registry in the package's
  initialization invariant), so that `raftOf rn r` reaches them.
- The term never wraps: each campaign takes a time receipt from raft's own Go steps, and the
  cluster invariant bounds every term by the receipts taken (the execution's step bound, fixed by the
  adequacy theorem, `notes/bounds-plan.md`); the same for indices (each appended entry costs a step).
  R1's `cluster_alloc` is where that bound enters (open question in `batch-R2.md`).

## Requirement snippets

`examples/specreq/raftcore/` (`//go:build ignore`, package `raft`: the calls are to unexported
functions): `step.go` (the sources of a step, the only error), `ready.go` (`node.run`'s `Ready`
handling: computed, stale, handed out, accepted, advanced; `RawNode.Ready` twice without `Advance`
panics), `conf.go` (`applyConfChange` after a decision; the snapshot's configuration at `Advance`),
`status.go` (the getters `node.run` and `RawNode` use; the field reads of `node.run`).
-/
module

public import Spec.go_etcd_io.raft.v3.Api

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

/-- Where an acknowledgement goes in a `Step` (`StepSrc`): a message from outside raft.go's own
`Ready` machinery, or an acknowledgement `acceptReady` queued for `Advance` (with the `RawNode` it
belongs to, the driver state after the batch was entered, the storage-write index and the
configuration view). -/
inductive StepSrc where
  | outside
  | ack (rn : Loc) (st : Driver) (k : Nat) (v : ConfView)

/-- The local message types that need no resource: the timers' (`MsgHup`, `MsgBeat`,
`MsgCheckQuorum`) and the node API's reports (`ReportUnreachable`, `ReportSnapshot`,
`TransferLeader`, `ForgetLeader`, `Campaign`). -/
def isReportType (t : w32) : Bool :=
  decide (t ∈ [MsgHup, MsgBeat, MsgCheckQuorum, MsgUnreachable, MsgSnapStatus, MsgTransferLeader,
    MsgForgetLeader])

/-- `LocalAppendThread`, `LocalApplyThread`. -/
def localAppendThread : w64 := W64 (2 ^ 64 - 1)
def localApplyThread : w64 := W64 (2 ^ 64 - 2)

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## raftpb's Go ownership this batch needs beyond R1's (provisional: batch 3h's) -/

/-- A `[]*Entry` slice (`dq` of it and of the entries) whose entries hold the terms, types and data
of `es` (any `Index`: a proposal's entries before `appendEntry` numbers them). -/
opaque entryPtrs (sl : GoSlice) (dq : DFrac) (es : List LogEntry) : IProp GF := iprop(True)

/-- The fresh memory of `getProgressCopy`'s map (its `Progress` values and their cloned
`Inflights`): part of R1's `statusOwn`. -/
opaque progressCopyOwn (mp : Loc) : IProp GF := iprop(True)

/-! ## The raft struct -/

/-- **The raft struct `r` of node `id` of `γ`**, of which its callers read `ρ`. Exclusive. -/
opaque raftCore (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) : IProp GF := iprop(True)

/-- `RawNode` `rn`'s raft struct is `r` (its `raft` field, never written after `NewRawNode`).
Persistent. -/
def raftOf (rn r : Loc) : IProp GF :=
  iprop(typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"raft" rn) r DFrac.discard)

/-- **A raft struct fresh from `newRaft`**, at view `ρ`, not yet in a `RawNode`: the node-level
start state (driver `st`, configuration view `v`, storage `S`, applied index `i`, storage snapshot
index `j`), one-shot (`raftBoot_bind`). -/
opaque raftBoot (r : Loc) (γ : Cluster) (ρ : CoreView) (st : Driver) (v : ConfView)
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
- received from a node of `γ`, addressed to `id`, with its credit;
- a local proposal (unstamped, from no one or `id`), each entry with its client's update or raft's
  own (a filler, the auto-leave entry), its conf-change entries decoding;
- a local read (unstamped, one entry: the registered context);
- a local timer or report message (unstamped). -/
def stepIn (γ : Cluster) (id : w64) (m : Msg) : IProp GF :=
  iprop((msgSent γ m ∗ msgCredit γ m ∗ ⌜m.to = id⌝) ∨
    (⌜m.type = MsgProp ∧ m.term = W64 0 ∧ (m.src = W64 0 ∨ m.src = id) ∧ m.entries ≠ [] ∧
        ∀ e ∈ m.entries, e.isConfChange → (decodeConfChange e.type e.data).isSome⌝ ∗
      [∗list] e ∈ m.entries, ⌜e.isFiller ∨ e.isEmptyV2⌝ ∨ propUpd γ e) ∨
    (∃ (e : LogEntry) (Q : List LogEntry → IProp GF),
      ⌜m.type = MsgReadIndex ∧ m.term = W64 0 ∧ (m.src = W64 0 ∨ m.src = id) ∧
        m.entries = [e]⌝ ∗ readCtx γ e.data Q) ∨
    ⌜m.term = W64 0 ∧ isReportType m.type = true⌝)

/-- **An acknowledgement `acceptReady` queued** in `RawNode` `rn` (the node's own vote or append
response, the storage-append response with the batch's last entry and snapshot, the apply response
with the batch's committed entries). Exclusive: stepped once. -/
opaque ackOk (rn : Loc) (γ : Cluster) (m : Msg) : IProp GF := iprop(True)

/-- What stepping an acknowledgement needs, besides `ackOk`: the batch entered (the driver back from
its `readyEnter`, at `st`) and its storage writes done; for the apply response, the configuration
view consistent with the delivered log (its conf entries past the view decided skip, as R1's
`Advance` takes). -/
def ackPre (rn : Loc) (γ : Cluster) (st : Driver) (k : Nat) (v : ConfView) (m : Msg) : IProp GF :=
  iprop(ackOk rn γ m ∗ nodeDriver rn γ st ∗ readyStor rn none k [] ∗ nodeConf rn γ v ∗
    (if m.type = MsgStorageApplyResp then confSkipped γ st.delivered v.applied st.delivered.length
     else True))

/-- What stepping it gives: the applied index at the delivered log (apply response); a snapshot's
configuration in force (the one at a committed point at or after its index, R1's `snapValid`), the
snapshot done in the driver (storage-append response carrying it). -/
def ackPost (rn : Loc) (γ : Cluster) (st : Driver) (k : Nat) (v : ConfView) (m : Msg) : IProp GF :=
  iprop(readyStor rn none k [] ∗
    match m.snapshot with
    | some s => nodeDriver rn γ { st with lastSnap := none } ∗ appliedLb rn (uint.nat s.index) ∗
        ∃ a mm, nodeConf rn γ ⟨a, mm⟩ ∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is mm⌝
    | none => nodeDriver rn γ st ∗ nodeConf rn γ v ∗
        (if m.type = MsgStorageApplyResp then appliedLb rn st.delivered.length else True))

/-- `raft.Step`'s precondition by source (`r` the raft struct). -/
def stepPre (r : Loc) (γ : Cluster) (id : w64) (m : Msg) : StepSrc → IProp GF
  | .outside => stepIn γ id m
  | .ack rn st k v => iprop(raftOf rn r ∗ ackPre rn γ st k v m)

/-- `raft.Step`'s postcondition by source. -/
def stepPost (γ : Cluster) (m : Msg) : StepSrc → IProp GF
  | .outside => iprop(True)
  | .ack rn st k v => ackPost rn γ st k v m

/-! ## The `RawNode`'s `Ready` phases (`rawnode.go`'s internals) -/

/-- **R1's `rawNode rn γ id` after `k` accepted `Ready`s**, with acknowledgements queued for
`Advance` iff `adv` (`rawNode_at`). Exclusive. -/
opaque rawNodeAt (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) : IProp GF :=
  iprop(True)

/-- **`rawNodeAt rn γ id k adv`, with `rd` the `Ready` of its current state** (computed by
`readyWithoutAccept`, nothing stepped since). Exclusive. -/
opaque readyFresh (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool)
    (rd : go_etcd_io.raft.v3.Ready) : IProp GF := iprop(True)

/-- `rd` was computed by `readyWithoutAccept` after `k` accepted `Ready`s. Persistent. -/
opaque readyKept (rn : Loc) (k : Nat) (rd : go_etcd_io.raft.v3.Ready) : IProp GF := iprop(True)

/-- **`Ready` `rd` handed out** (`ready_handout`), its `acceptReady` due. Exclusive. -/
opaque readyHanded (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (rd : go_etcd_io.raft.v3.Ready) :
    IProp GF := iprop(True)

/-! ## Internal: cluster facts raft.go's handlers use -/

/-- **`l` won the election of term `t`** (its candidacy's votes, a quorum of its configuration).
Persistent. -/
opaque leaderOf (γ : Cluster) (t : w64) (l : w64) : IProp GF := iprop(True)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

def core_persistent.spec : Prop :=
  (∀ rn k rd, Persistent (readyKept (GF := GF) rn k rd)) ∧
  (∀ γ t l, Persistent (leaderOf (GF := GF) γ t l))

def raftCore_exclusive.spec : Prop :=
  ∀ r γ id ρ γ' id' ρ', raftCore (GF := GF) r γ id ρ ∗ raftCore r γ' id' ρ' ⊢ iprop(False)

/-- **Election safety**: a term has at most one leader. -/
def leaderOf_agree.spec : Prop :=
  ∀ γ t (l1 l2 : w64), leaderOf (GF := GF) γ t l1 ∗ leaderOf γ t l2 ⊢ iprop(⌜l1 = l2⌝)

/-- Only the leader of a term sends appends, heartbeats, snapshots and `MsgTimeoutNow` in it. -/
def msgSent_leaderOf.spec : Prop :=
  ∀ γ (m : Msg), m.type ∈ [MsgApp, MsgHeartbeat, MsgSnap, MsgTimeoutNow] →
    msgSent (GF := GF) γ m ⊢ leaderOf γ m.term m.src

/-- **The fields `node.run` reads** (`r.lead`, `r.Term`, `r.id`, `r.logger`, `r.trk.Progress`,
`r.tick`), given back unchanged. -/
def raftCore_peek.spec : Prop :=
  ∀ r γ id ρ, raftCore (GF := GF) r γ id ρ ⊢
    ∃ mp, raftPeek r id ρ mp ∗ (raftPeek r id ρ mp -∗ raftCore r γ id ρ)

/-- **Binding a fresh raft struct to its `RawNode`** (`NewRawNode`): with the `RawNode`'s fields
as `NewRawNode` sets them (its raft struct, synchronous storage writes, the soft and hard state of
the view raft started at, no acknowledgement queued), the `RawNode`'s token and R1's node
predicates keyed by it. -/
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

/-- **The raft struct of a `RawNode`**: open to call its methods; closed again at any view (a step
does not change the phase). -/
def rawNodeAt_core.spec : Prop :=
  ∀ rn γ id k adv, rawNodeAt (GF := GF) rn γ id k adv ⊢
    ∃ r ρ, raftOf rn r ∗ raftCore r γ id ρ ∗ (∀ ρ', raftCore r γ id ρ' -∗ rawNodeAt rn γ id k adv)

/-- **The acknowledgements queued for `Advance`** (`rn.stepsOnAdvance`, `RawNode.Advance`'s loop):
each with its `ackOk` (none unless `adv`); with the field at an empty slice of the same backing
array, the `RawNode` has none queued. -/
def rawNodeAt_advance.spec : Prop :=
  ∀ rn γ id k adv, rawNodeAt (GF := GF) rn γ id k adv ⊢
    ∃ (sl : GoSlice) (ps : List Loc) (ms : List Msg),
      typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"stepsOnAdvance" rn) sl
        (DFrac.own 1) ∗
      ownSlice sl ps (DFrac.own 1) ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
      ⌜ps.length = ms.length ∧ (adv = false → ms = [])⌝ ∗
      ([∗list] pm ∈ ps.zip ms, msgPts pm.1 (DFrac.own 1) pm.2 ∗ ackOk rn γ pm.2) ∗
      (∀ (sl' : GoSlice) (ps' : List Loc),
        typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"stepsOnAdvance" rn) sl'
          (DFrac.own 1) ∗ ownSlice sl' ps' (DFrac.own 1) ∗ ownSliceCap Loc sl' (DFrac.own 1) ∗
          ⌜ps' = []⌝ -∗ rawNodeAt rn γ id k false)

/-- A fresh `Ready` stops being fresh when anything is stepped: what remains is the token and the
persistent record that it was computed in this phase. -/
def readyFresh_forget.spec : Prop :=
  ∀ rn γ id k adv rd, readyFresh (GF := GF) rn γ id k adv rd ⊢
    rawNodeAt rn γ id k adv ∗ readyKept rn k rd

/-- **Handing a `Ready` out** (`node.run`'s send on `readyc`, inside the receive's update;
`RawNode.Ready`): a fresh `Ready` computed with no acknowledgement pending, at the client's driver
state, gives R1's `readyGot` (the batch, its facts, the messages' credits, the storage writes, the
enter and check updates) and leaves its `acceptReady` due. -/
def ready_handout.spec : Prop :=
  ∀ rn γ id k rd (st : Driver),
    readyFresh (GF := GF) rn γ id k false rd ∗ nodeDriver rn γ st ⊢ |==>
      readyHanded rn γ id k rd ∗ readyGot rn γ id st rd

end laws

end Raft
end EtcdGrove
end Perennial
