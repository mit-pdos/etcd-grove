/-
Port of `election_proof/inv_rawnode.v` (at 857d09190), reworked on 2026-10-09.

**The `RawNode`, as its client sees it (2026-10-09)**

`ownRawNode γ rn id rs` is the one predicate for a `RawNode` (`rawnode.go`), and it is
**protocol-free**: its index `rs : RNState` is what the application sees -- the committed
log handed out so far (`delivered`), the entries handed out that it must still append to
storage (`unpersisted`), the local messages `Advance` will step (`steps`, opaque) and
whether `Advance` is proved for them (`advanceable`, the gap described there). Inside
are the struct, the `raft` it points to at some physical state `s` (`ownRaftPhys`), the
node's ghost state at some protocol state `ps` (`ownRaftGhost`, `NStateRel s ps`), and
the facts that tie `rs` to `s`: `isCommitted γ rs.delivered` with `delivered` as long as
`applying`, `rs.unpersisted = s.logst.unpersisted`, and `StepsOk` for an advanceable
queue. The scope facts the specs took as premises until then are conjuncts: the node
is a voter of `γ.reCfg`, the configuration `ownRaftPhys` is about; no snapshot is
pending (handing one out is phase 2); synchronous storage writes.

Until 2026-10-08 the predicate was `ownRawNode cfg rn id s rs`, indexed by the node's
`NState` and an `RNState` of the previous `SoftState`/`HardState` and the queue, with
the ghost state beside it in every spec; the specs exposed the protocol state
(`NStateRel`, `Step`, `ps.role`, `s.logst.applying`, ...). The previous `SoftState` and
`HardState` are now owned and unconstrained (`prevSoftSt` points to some `SoftState`,
read-only): no spec states them.

With synchronous storage writes `Ready`'s `acceptReady` queues the self-addressed
responses of `msgsAfterAppend`, a `MsgStorageAppendResp` and a `MsgStorageApplyResp`
into `stepsOnAdvance`, and `Advance` steps them. The log-side notions `Ready`/`Advance`
are proved with -- the next unstable entries, the committed entries to apply,
`acceptUnstable`, `stableTo` -- are pure functions of `LogState` in `InvReadylog.lean`.

Lean notes: the Rocq records `hardstate.t`, `softstate.t`, `rnstate.t` and the
inductive `pending.t` are `HardSt`, `SoftSt`, `RNState`, `Pending` (`HardSt`/`SoftSt`
after the Go fields `prevHardSt`/`prevSoftSt`: `SoftState` is the Goose type of
`go_etcd_io.raft.v3`, opened here; they are the proofs' now, no spec mentions them); the
constructors `pending.self`, `pending.append_ack`, `pending.apply_ack` are
`Pending.self`, `.appendAck`, `.applyAck`. `hs_abs`, `hs_empty_abs`, `node_hardstate`,
`node_softstate`, `hardstate_val`, `softstate_val`, `append_ack_msg`, `apply_ack_msg`,
`pending_rel`, `pending_own`, `own_RawNode` are `hsAbs`, `hsEmptyAbs`, `nodeHardstate`,
`nodeSoftstate`, `hardstateVal`, `softstateVal`, `appendAckMsg`, `applyAckMsg`,
`pendingRel`, `pendingOwn`, `ownRawNode`; the `EqDecision` instances are `deriving
DecidableEq`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The RawNode's state -/

structure HardSt where
  term : w64
  vote : w64
  commit : w64
deriving DecidableEq

structure SoftSt where
  lead : w64
  /-- `StateType` -/
  state : w64
deriving DecidableEq

/-- A local message `acceptReady` queued for `Advance` to step:

- `self a`: a self-addressed response from `msgsAfterAppend` (the candidate's own vote,
  the leader's own `MsgAppResp`), abstracted as `a`;
- `appendAck t last`: `MsgStorageAppendResp` at term `t` acknowledging the log up to
  `last` (queued when there were unstable entries);
- `applyAck ents`: `MsgStorageApplyResp` carrying the committed entries handed out for
  applying. -/
inductive Pending [FfiSyntax] where
  | self (a : Option Msg)
  | appendAck (term : w64) (last : entryID)
  | applyAck (ents : List raftpb.Entry)

/-- What the application sees of a `RawNode` (2026-10-09). -/
structure RNState [FfiSyntax] where
  /-- The committed log handed out so far, from the start (as `isCommitted` takes it):
  every `Ready`'s `CommittedEntries`, in order, after the entries applied before the
  node was built. -/
  delivered : List raftpb.Entry
  /-- The entries `Ready` handed out (`Ready.Entries`) that the application must still
  append to the `Storage` (`ownRawNode_persist`). -/
  unpersisted : List raftpb.Entry
  /-- `rn.stepsOnAdvance`: what `Advance` will step. Opaque to clients, which only
  learn that it is empty (after `Advance`), as `Ready` requires. -/
  steps : List Pending
  /-- Whether `Advance` is proved for `steps`. **A gap, to be closed**: `Advance`'s spec
  covers only a queue without self-addressed responses (`Pending.self`: a candidate's
  own vote, a leader's own `MsgAppResp`, which `msgsAfterAppend` produces), because
  `Step`'s spec asks of each message facts the raft struct does not record for the
  queue. `Ready` returns it (its proof sets it to `true` exactly when it queued none;
  the postcondition does not say when, which is protocol state). So a client cannot
  establish `advanceable = true`: until the gap is closed it can call `Ready` once and
  then neither `Advance` (unproved) nor `Ready` (which needs `steps` empty). See
  `RawNode.Advance.spec`. -/
  advanceable : Bool
  /-- The node's current term (2026-10-09). A client sees it (`Status`, `Ready`'s
  `HardState`); the specs need it because Go panics when a campaign wraps it
  (`Campaign`, `Tick`), and say how a step moves it. -/
  term : w64

section defs
variable [FfiSyntax]

def hsAbs (h : raftpb.HardState) : HardSt :=
  ⟨h.Term', h.Vote', h.Commit'⟩

def hsEmptyAbs (h : HardSt) : Bool :=
  decide (h.term = W64 0 ∧ h.vote = W64 0 ∧ h.commit = W64 0)

/-- `r.hardState()` and `r.softState()` of a node in physical state `s`. -/
def nodeHardstate (s : NState) : HardSt :=
  ⟨s.term, s.vote, s.logst.committed⟩
def nodeSoftstate (s : NState) : SoftSt :=
  ⟨s.lead, stateW64 s.role⟩

def hardstateVal (h : HardSt) : raftpb.HardState :=
  raftpb.HardState.mk h.term h.vote h.commit
def softstateVal (h : SoftSt) : SoftState :=
  SoftState.mk h.lead h.state

/-- The two local messages, as `newStorageAppendRespMsg` and `newStorageApplyRespMsg`
build them (with synchronous writes and no pending snapshot). -/
def appendAckMsg (id t : w64) (e : entryID) : raftpb.Message :=
  raftpb.Message.mk MsgStorageAppendResp id LocalAppendThread t
    e.term' e.index' slice.nil (W64 0) (W64 0) null false (W64 0) slice.nil slice.nil

def applyAckMsg (id : w64) (sl : GoSlice) : raftpb.Message :=
  raftpb.Message.mk MsgStorageApplyResp id LocalApplyThread (W64 0) (W64 0) (W64 0) sl
    (W64 0) (W64 0) null false (W64 0) slice.nil slice.nil

/-! ## The queue `Advance` is proved for

What `Advance` needs of the queue it steps, at the state `s` it is called in, stated so
that `Ready` establishes it and a `Propose` in between keeps it (`stepsOk_mono`). -/

/-- A queued `MsgStorageApplyResp`: its entries end at or below `committed` (`Step`'s
premise, `appliedTo`'s guard) and at or below `applying` (so that its `appliedTo` does
not move `applying`, to which `RNState.delivered` is tied). -/
def ApplyAckOk (s : NState) (p : Pending) : Prop :=
  match p with
  | .applyAck ce => ∀ e, ce.getLast? = some e →
      uint.Z e.Index' ≤ uint.Z s.logst.committed ∧ uint.Z e.Index' ≤ uint.Z s.logst.applying
  | _ => False

/-- One queued message, steppable at `s`: a `MsgStorageAppendResp` not from a later term
whose index is in progress (with nothing unpersisted and no snapshot pending, that is
`StableOk`: `Ready`'s `ready_stable_ok`), or an `ApplyAckOk` `MsgStorageApplyResp`;
never a self-addressed response. -/
def PendingOk (s : NState) (p : Pending) : Prop :=
  match p with
  | .appendAck t e => uint.Z t ≤ uint.Z s.term ∧ uint.Z e.index' < uint.Z s.logst.inprogress
  | .applyAck _ => ApplyAckOk s p
  | .self _ => False

/-- The queue: the `MsgStorageAppendResp`, if any, first (as `acceptReady` queues it),
then `ApplyAckOk` ones; no self-addressed response (the gap, `RNState.advanceable`).
Until 2026-10-09 `AdvanceOk`, a premise of `Advance`'s spec. -/
def StepsOk (s : NState) (steps : List Pending) : Prop :=
  match steps with
  | .appendAck t e :: rest => PendingOk s (.appendAck t e) ∧ ∀ p ∈ rest, ApplyAckOk s p
  | _ => ∀ p ∈ steps, ApplyAckOk s p

theorem applyAckOk_mono (s s' : NState) (p : Pending)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (Ha : s'.logst.applying = s.logst.applying) :
    ApplyAckOk s p → ApplyAckOk s' p := by
  cases p with
  | applyAck ce =>
    intro H e He
    have := H e He
    rw [Ha]
    omega
  | _ => intro H; exact H

/-- `StepsOk` survives a step that keeps the term and `applying` and moves neither
`offsetInProgress` nor `committed` back -- a `Propose`'s (`LocalStepOk`,
`Step.commit_mono`), or the application's append (`ownRawNode_persist`). -/
theorem stepsOk_mono (s s' : NState) (steps : List Pending)
    (Ht : s'.term = s.term)
    (Hi : uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (Ha : s'.logst.applying = s.logst.applying) :
    StepsOk s steps → StepsOk s' steps := by
  have Hall : ∀ l : List Pending, (∀ p ∈ l, ApplyAckOk s p) → ∀ p ∈ l, ApplyAckOk s' p :=
    fun l H p Hp => applyAckOk_mono s s' p Hc Ha (H p Hp)
  match steps with
  | .appendAck t e :: rest =>
    intro ⟨⟨H1, H2⟩, Hr⟩
    exact ⟨⟨by rw [Ht]; exact H1, by omega⟩, Hall rest Hr⟩
  | [] => intro H; exact Hall [] H
  | .self a :: rest => intro H; exact Hall _ H
  | .applyAck ce :: rest => intro H; exact Hall _ H

/-- `StepsOk` survives a step that moves the term up (a campaign, a message of a higher
term: `TermStep`), keeps `applying`, and moves neither `offsetInProgress` nor `committed`
back: a queued `MsgStorageAppendResp` of an older term is still not from a later one. -/
theorem stepsOk_mono_le (s s' : NState) (steps : List Pending)
    (Ht : uint.Z s.term ≤ uint.Z s'.term)
    (Hi : uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (Ha : s'.logst.applying = s.logst.applying) :
    StepsOk s steps → StepsOk s' steps := by
  have Hall : ∀ l : List Pending, (∀ p ∈ l, ApplyAckOk s p) → ∀ p ∈ l, ApplyAckOk s' p :=
    fun l H p Hp => applyAckOk_mono s s' p Hc Ha (H p Hp)
  match steps with
  | .appendAck t e :: rest =>
    intro ⟨⟨H1, H2⟩, Hr⟩
    exact ⟨⟨by omega, by omega⟩, Hall rest Hr⟩
  | [] => intro H; exact Hall [] H
  | .self a :: rest => intro H; exact Hall _ H
  | .applyAck ce :: rest => intro H; exact Hall _ H

/-- The head of a `StepsOk` queue is steppable now, and the rest stays `StepsOk` at any
state with a commit index no smaller and the same `applying`. -/
theorem stepsOk_cons (s : NState) (p : Pending) (rest : List Pending) :
    StepsOk s (p :: rest) →
    PendingOk s p ∧
    ∀ s' : NState, uint.Z s.logst.committed ≤ uint.Z s'.logst.committed →
      s'.logst.applying = s.logst.applying → StepsOk s' rest := by
  have Hrest : ∀ s' : NState, uint.Z s.logst.committed ≤ uint.Z s'.logst.committed →
      s'.logst.applying = s.logst.applying →
      (∀ q ∈ rest, ApplyAckOk s q) → StepsOk s' rest := by
    intro s' Hc Ha Hr
    have Hr' : ∀ q ∈ rest, ApplyAckOk s' q :=
      fun q Hq => applyAckOk_mono s s' q Hc Ha (Hr q Hq)
    match rest, Hr' with
    | [], _ => intro q Hq; cases Hq
    | .appendAck t e :: _, Hr' => exact absurd (Hr' _ List.mem_cons_self) id
    | .self a :: _, Hr' => exact (Hr' _ List.mem_cons_self).elim
    | .applyAck ce :: _, Hr' => exact Hr'
  cases p with
  | self a =>
    intro H
    exact (H _ List.mem_cons_self).elim
  | appendAck t e =>
    intro ⟨Hh, Hr⟩
    exact ⟨Hh, fun s' Hc Ha => Hrest s' Hc Ha Hr⟩
  | applyAck ce =>
    intro H
    exact ⟨H _ List.mem_cons_self, fun s' Hc Ha =>
      Hrest s' Hc Ha (fun q Hq => H q (List.mem_cons_of_mem _ Hq))⟩

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The physical message queued for a pending step. -/
def pendingRel (id : w64) (m : raftpb.Message) (p : Pending) : IProp GF :=
  match p with
  | .self a => iprop(msgAbs m a ∗ ⌜m.To' = id⌝)
  | .appendAck t e => iprop(⌜m = appendAckMsg id t e⌝)
  | .applyAck ents => iprop(∃ sl, ⌜m = applyAckMsg id sl⌝ ∗ sl ↦*□ ents)

instance pendingRel_pers (id : w64) (m : raftpb.Message) (p : Pending) :
    Persistent (pendingRel (GF := GF) id m p) := by
  cases p <;> unfold pendingRel <;> infer_instance

/-- What a pending step owns: the capacity of a `MsgStorageApplyResp`'s `Entries` --
`Ready`'s `CommittedEntries` slice, which `Step`'s spec asks to own and which `Ready`
therefore keeps for the node rather than handing to the application. -/
def pendingOwn (m : raftpb.Message) (p : Pending) : IProp GF :=
  match p with
  | .applyAck _ => ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)
  | _ => iprop(True)

end proof

section rawnode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`: the predicate holds the ghost state (`ownRaftGhost`), as in
-- `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- A message `Ready` hands to the application to send: what it contributes to the
protocol's messages (`msgAbs`: nothing, for a type the protocol does not describe) was
legitimately sent (`isMessage`). -/
def isRaftMsg (γ : RaftNames) (m : raftpb.Message) : IProp GF :=
  iprop(∃ a, msgAbs m a ∗ [∗list] x ∈ a.toList, isMessage γ x)

instance isRaftMsg_pers (γ : RaftNames) (m : raftpb.Message) :
    Persistent (isRaftMsg (GF := GF) γ m) := by
  unfold isRaftMsg; infer_instance

/-! ## The one predicate for a `RawNode` -/

/-- See the file header. `s` and `ps` are the node's physical and protocol states;
`delivered` is the committed log up to `applying` (`isCommitted_agree` makes it the one
such list), `unpersisted` the log's. -/
def ownRawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) : IProp GF :=
  iprop(∃ (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState)
      (steps : List raftpb.Message),
  "Hrn" ∷ rn ↦ rnv ∗
  "Hphys" ∷ ownRaftPhys γ.reCfg rnv.raft' id s ∗
  "Hghost" ∷ ownRaftGhost γ id ps ∗
  "%Hrel" ∷ ⌜NStateRel s ps⌝ ∗
  -- scope: the node is a voter (`Step`'s premise)
  "%Hin" ∷ ⌜id ∈ γ.reCfg⌝ ∗
  -- scope: synchronous storage writes (`Config.AsyncStorageWrites` unset); `NewRawNode`
  -- copies the `Config` field
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  -- `prevSoftSt`: a pointer to a `SoftState` nobody writes (it is either `NewRawNode`'s
  -- or a `Ready.SoftState`), held read-only; `prevHardSt` is a value of `rnv`
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hpend" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel id m p) ∗
  "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  -- scope: no snapshot pending (handing one out and `appliedSnap` are phase 2)
  "%Hsnap" ∷ ⌜s.logst.snap = none⌝ ∗
  "%Hadv" ∷ ⌜rs.advanceable = true → StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝)

/-- Closing the predicate; the pure premises are first, the resources in the order of
the definition. -/
theorem ownRawNode_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hadv : rs.advanceable = true → StepsOk s rs.steps)
    (Htrm : rs.term = s.term) :
    ⊢ rn ↦ rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s -∗ ownRaftGhost (GF := GF) γ id ps -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel id m p) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) -∗
      isCommitted γ rs.delivered -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsoft Hsteps Hcap #Hpend Hpown #Hdeliv
  unfold ownRawNode
  iexists s, ps, rnv, sv, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsoft Hsteps Hcap Hpend Hpown Hdeliv
  ipureintro
  exact ⟨Hrel, Hin, Hasync, Hdlen, Hunp, Hsnap, Hadv, Htrm⟩

/-- The storage handshake, at the RawNode: the `Storage` the log owns, for the
application to append the entries the last `Ready` handed out (`ownRaftLog_persist`,
`InvRaftlog.lean`); afterwards nothing is unpersisted. -/
theorem ownRawNode_persist (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ∃ (st : Storage) (σ : StorState),
        isStorage st ∗ ownStorage st σ ∗
        (ownStorage st { σ with ents := storApp σ rs.unpersisted } -∗
         ownRawNode γ rn id { rs with unpersisted := [] }) := by
  iintro H
  iNamed H
  icases ownRaftPhys_log_at γ.reCfg rnv.raft' id s $$ Hphys with ⟨Hlog, Hlback⟩
  icases ownRaftLog_persist s.log s.logst $$ Hlog with
    ⟨%st, %σ, #Hst, HSt, Hclose⟩
  rw [Hunp]
  iexists st, σ
  iframe Hst HSt
  iintro HSt
  ihave Hlog := Hclose $$ HSt
  ihave Hphys := Hlback $$ %_ Hlog
  iapply ownRawNode_intro γ rn id { rs with unpersisted := [] }
    { s with logst := { s.logst with unpersisted := [] } } ps rnv sv steps Hrel Hin Hasync
    Hdlen rfl Hsnap
    (fun h => stepsOk_mono s _ rs.steps rfl (Int.le_refl _) (Int.le_refl _) rfl (Hadv h))
    Htrm $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv

end rawnode

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.hsAbs Perennial.EtcdGrove.nodeHardstate Perennial.EtcdGrove.nodeSoftstate
