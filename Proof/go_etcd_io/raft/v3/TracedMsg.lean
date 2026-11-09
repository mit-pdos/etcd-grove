/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 4 (2026-11-09): the vocabulary of the message
hooks' specs (`traceEvent` with a message, `makeTracingMessage`, `traceSendMessage`,
`traceReceiveMessage`).

- `traceMsgOf ms`: the `TracingMessage` `makeTracingMessage` builds of a message holding `ms`
  (its type's name `raftpb.msgTypeString`, Q9; a `MsgSnap`'s entry count its snapshot's index);
  `msgEvOf_traceMsgOf`: for a traced type it is the Draft's `MsgEvOf` of the message's abstraction.
- `MsgArg`, `msgArg m om`: the message `traceEvent` is given (`none`: nil), at any fractions.
- `EvHdrOf`: what every event `traceEvent` builds says of raft's state (`NodeEvOf`'s and
  `SendEvOf`'s first conjuncts); `nodeEvOf_of_hdr`, `sendEvOf_of_hdr`.
- `RaftLend P …`, `MsgLend P …`: the hooks' lending form. A hook reads raft's state and the message
  in turn (`traceSendMessage`: the message's type, then raft's progress, then raft's state, then the
  message again), so its caller lends both out of one resource `P`, each through a persistent
  accessor; a caller holding the two separately takes `P` their conjunction (`raftLend_sep`,
  `msgLend_sep`). Stated so that a caller whose message is queued in raft's struct can lend it once
  an accessor exists that gives it out of `ownRaftPhysCV` (`notes/trace-validation-plan.md`, slice 4:
  not yet, `raft.send` is blocked on it).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedMsgType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A message's snapshot index as `m.GetSnapshot().GetMetadata().GetIndex()` reads it (`0` with no
snapshot). -/
def snapIdx (ms : MsgSt) : w64 :=
  match ms.snap with
  | none => W64 0
  | some sv => sv.Metadata'.Index'

/-- **The `TracingMessage` `makeTracingMessage(m)` builds** of a message holding `ms`: its type's
name, its term, its sender and receiver in decimal, its entry count (a `MsgSnap`'s: its snapshot's
index), log term and index (`0` for a `MsgSnap`), commit, vote in decimal, reject and hint. -/
def traceMsgOf (ms : MsgSt) : TraceMsg :=
  if ms.msg.Type' = MsgSnap then
    ⟨raftpb.msgTypeString ms.msg.Type', ms.msg.Term', decStr ms.msg.From', decStr ms.msg.To',
      snapIdx ms, W64 0, W64 0, ms.msg.Commit', decStr ms.msg.Vote', ms.msg.Reject',
      ms.msg.RejectHint'⟩
  else
    ⟨raftpb.msgTypeString ms.msg.Type', ms.msg.Term', decStr ms.msg.From', decStr ms.msg.To',
      W64 ms.ents.length, ms.msg.LogTerm', ms.msg.Index', ms.msg.Commit', decStr ms.msg.Vote',
      ms.msg.Reject', ms.msg.RejectHint'⟩

/-- **A traced message's event field is the Draft's `MsgEvOf`** of its abstraction. -/
theorem msgEvOf_traceMsgOf (ms : MsgSt) (ty : MsgType) (ctx : List w8)
    (h : mtypeOf ms.msg.Type' = some ty) (hs : sendEvt ty ≠ none) :
    MsgEvOf (absMsg ty ms.msg ms.ents ctx) (traceMsgOf ms) := by
  have hns : ms.msg.Type' ≠ MsgSnap := by
    intro he
    rw [he, mtypeOf_MsgSnap] at h
    cases h
    exact hs rfl
  unfold traceMsgOf MsgEvOf
  simp only [hns, ↓reduceIte]
  refine ⟨msgTypeString_traced _ ty h hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `traceMsgOf`'s vote is a decimal. -/
theorem traceMsgOf_vote (ms : MsgSt) : ∃ v : w64, (traceMsgOf ms).vote = decStr v := by
  unfold traceMsgOf
  split <;> exact ⟨ms.msg.Vote', rfl⟩

/-- **What every event `traceEvent` builds says of raft's state** (the first conjuncts of
`NodeEvOf` and `SendEvOf`): its name, node, hard state, role, last index and configuration. -/
def EvHdrOf (evt : w64) (id : w64) (s : NState) (c : CfgM) (e : TraceEv) : Prop :=
  evtNames[uint.nat evt]? = some e.name ∧
  e.nid = decStr id ∧ e.term = s.term ∧ e.vote = decStr s.vote ∧ e.commit = s.logst.committed ∧
  e.role = roleStr s.role ∧ e.logSize = plastIndex (toPState s) ∧
  (∃ xs ys : List w64, xs ≡ₚ elements c.incoming ∧ ys ≡ₚ elements c.outgoing ∧
    e.conf = (xs.map decStr, ys.map decStr))

/-- A node event: the header and nothing else. -/
theorem nodeEvOf_of_hdr {evt id : w64} {s : NState} {c : CfgM} {e : TraceEv}
    (h : EvHdrOf evt id s c e) (hm : e.msg = none) (hc : e.cc = none) (hpc : e.propCC = none)
    (hpm : e.propMatch = none) (hpn : e.propNext = none) : NodeEvOf evt id s c e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hm, hc, hpc, hpm, hpn⟩

/-- A send (or receive) event of a traced message: the header and the message's `traceMsgOf`. -/
theorem sendEvOf_of_hdr {evt id : w64} {s : NState} {c : CfgM} {e : TraceEv} (ms : MsgSt)
    (ty : MsgType) (ctx : List w8) (hty : mtypeOf ms.msg.Type' = some ty) (hs : sendEvt ty ≠ none)
    (h : EvHdrOf evt id s c e) (hm : e.msg = some (traceMsgOf ms)) (hc : e.cc = none)
    (hpc : e.propCC = none) : SendEvOf evt id s c (absMsg ty ms.msg ms.ents ctx) e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ⟨_, hm, msgEvOf_traceMsgOf ms ty ctx hty hs⟩, hc, hpc, ?_⟩
  intro tm htm
  rw [hm] at htm
  cases htm
  exact traceMsgOf_vote ms

/-- An event with no properties (`traceEvent`'s `e0` for a nil `prop`). -/
def noProps : TraceEv :=
  ⟨go!"", go!"", W64 0, go!"", W64 0, go!"", W64 0, ([], []), none, none, none, none, none⟩

/-- `recvEvt` traces the types `sendEvt` does. -/
theorem sendEvt_of_recvEvt {ty : MsgType} (h : recvEvt ty ≠ none) : sendEvt ty ≠ none := by
  cases ty <;> simp_all [sendEvt, recvEvt]

/-- The send hook's gate at a type it traces. -/
theorem sendGate_of {id : w64} {s : NState} {c : CfgM} {ms : MsgSt} {ty : MsgType} {evt : w64}
    (h : mtypeOf ms.msg.Type' = some ty) (he : sendEvt ty = some evt) :
    sendGate id s c ms = some (SendEvOf evt id s c (absMsg ty ms.msg ms.ents)) := by
  unfold sendGate; rw [h]; simp [he]

/-- ... at a type it does not trace. -/
theorem sendGate_none_of {id : w64} {s : NState} {c : CfgM} {ms : MsgSt}
    (h : ∀ ty, mtypeOf ms.msg.Type' = some ty → sendEvt ty = none) : sendGate id s c ms = none := by
  unfold sendGate
  cases ht : mtypeOf ms.msg.Type' with
  | none => rfl
  | some ty => simp [h ty ht]

/-- The receive hook's gate at a type it traces. -/
theorem recvGate_of {id : w64} {s : NState} {c : CfgM} {ms : MsgSt} {ty : MsgType} {evt : w64}
    (h : mtypeOf ms.msg.Type' = some ty) (he : recvEvt ty = some evt) :
    recvGate id s c ms = some (SendEvOf evt id s c (absMsg ty ms.msg ms.ents)) := by
  unfold recvGate; rw [h]; simp [he]

/-- ... at a type it does not trace. -/
theorem recvGate_none_of {id : w64} {s : NState} {c : CfgM} {ms : MsgSt}
    (h : ∀ ty, mtypeOf ms.msg.Type' = some ty → recvEvt ty = none) : recvGate id s c ms = none := by
  unfold recvGate
  cases ht : mtypeOf ms.msg.Type' with
  | none => rfl
  | some ty => simp [h ty ht]

/-- The types the hooks' `switch` tests: a type none of them is traced by neither hook. -/
theorem untraced_type {t : w32}
    (h : t ≠ W32 3 ∧ t ≠ W32 4 ∧ t ≠ W32 5 ∧ t ≠ W32 6 ∧ t ≠ W32 7 ∧ t ≠ W32 8 ∧ t ≠ W32 9) :
    ∀ ty, mtypeOf t = some ty → sendEvt ty = none ∧ recvEvt ty = none := by
  intro ty hty
  obtain ⟨h3, h4, h5, h6, h7, h8, h9⟩ := h
  unfold mtypeOf at hty
  split at hty <;> rename_i hz <;> cases hty <;> simp only [sendEvt, recvEvt, and_self] <;>
    first
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h3
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h4
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h5
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h6
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h7
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h8
    | exact absurd (uint_Z_inj.1 (by rw [hz]; rfl)) h9


/-- (Q8 stage 1, slice 5) **`raft.send`'s hook's events**, by the message's type `ty` and what the
outbox grows by (`out`, `SendOk`'s): for a traced type (`sendEvt`), a `SendEvOf` event of one of
`out`'s messages at the sender's state `s` (the state before the message is queued: the event's
header reads none of what `send` changes); none for another type. -/
def sendOutGate (id : w64) (s : NState) (c : CfgM) (ty : w32) (out : List Msg) :
    Option (TraceEv → Prop) :=
  ((mtypeOf ty).bind sendEvt).map (fun evt e => ∃ mm ∈ out, SendEvOf evt id s c mm e)

/-- (Q8 stage 1, slice 5) **The hook's gate at the queued message is within `send`'s**: the hook
logs at the state with the message queued (`{ s with outbox := o, gh := g }`), whose event header is
`s`'s, and the queued message `ms` (stamped) is, as `MsgEvOf` reads it, one of `out`'s. -/
theorem sendGate_le (id : w64) (s : NState) (o : List Msg) (g : NGhost) (c : CfgM) (ms : MsgSt)
    (ty : w32) (out : List Msg) (hty : ms.msg.Type' = ty)
    (hout : ∀ t evt, mtypeOf ty = some t → sendEvt t = some evt →
      ∃ mm ∈ out, ∀ tm, MsgEvOf (absMsg t ms.msg ms.ents) tm → MsgEvOf mm tm) :
    (sendOutGate id s c ty out = none ↔ sendGate id { s with outbox := o, gh := g } c ms = none) ∧
    ∀ E E', sendOutGate id s c ty out = some E → sendGate id { s with outbox := o, gh := g } c ms = some E' →
      ∀ e, E' e → E e := by
  unfold sendOutGate sendGate
  rw [hty]
  cases ht : mtypeOf ty with
  | none => simp
  | some t =>
    cases hev : sendEvt t with
    | none => simp [hev]
    | some evt =>
      simp only [Option.bind_some, hev, Option.map_some, reduceCtorEq, iff_self, true_and,
        Option.some.injEq]
      rintro E E' rfl rfl e ⟨h1, h2, h3, h4, h5, h6, h7, h8, ⟨tm, h9, h10⟩, h11, h12, h13⟩
      obtain ⟨mm, hmm, hm⟩ := hout t evt ht hev
      exact ⟨mm, hmm, h1, h2, h3, h4, h5, h6, h7, h8, ⟨tm, h9, hm tm h10⟩, h11, h12, h13⟩

end pure

/-! ## The message argument and the lending form -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The message a hook is given, at its fractions (`msgPtsC`'s). -/
structure MsgArg [GooseExts] where
  dq : DFrac
  dqe : DFrac
  cap : Bool
  ms : MsgSt

/-- `traceEvent`'s message: nil (`none`) or a message holding `a.ms`. -/
def msgArg (m : Loc) : Option MsgArg → IProp GF
  | none => iprop(⌜m = null⌝)
  | some a => msgPtsC m a.dq a.dqe a.cap a.ms

/-- The event's message field of `traceEvent`'s message. -/
def msgArgTrace : Option MsgArg → Option TraceMsg
  | none => none
  | some a => some (traceMsgOf a.ms)

/-- The properties' representation reads only the event's three properties. -/
theorem tracingPropsRep_congr (m : GoMap) (e e' : TraceEv) (h1 : e.propCC = e'.propCC)
    (h2 : e.propMatch = e'.propMatch) (h3 : e.propNext = e'.propNext) :
    tracingPropsRep (GF := GF) m e ⊣⊢ tracingPropsRep m e' := by
  unfold tracingPropsRep
  rw [h1, h2, h3]
  exact .rfl

/-- ... as a wand. -/
theorem tracingPropsRep_of (m : GoMap) (e e' : TraceEv) (h1 : e.propCC = e'.propCC)
    (h2 : e.propMatch = e'.propMatch) (h3 : e.propNext = e'.propNext) :
    ⊢ tracingPropsRep (GF := GF) m e' -∗ tracingPropsRep m e := by
  iintro H
  iapply (tracingPropsRep_congr m e e' h1 h2 h3).2
  iexact H

variable [StorageModel GF] [go_etcd_io.raft.v3.Assumptions]

/-- **Raft's state, lent out of `P`** (persistently: a hook may read it more than once). -/
def RaftLend (P : IProp GF) (c : CfgM) (r : Loc) (id : w64) (s : NState) : IProp GF :=
  iprop(□ (P -∗ ownRaftPhysCV c c.voters r id s ∗ (ownRaftPhysCV c c.voters r id s -∗ P)))

/-- **The message, lent out of `P`**. -/
def MsgLend (P : IProp GF) (m : Loc) (om : Option MsgArg) : IProp GF :=
  iprop(□ (P -∗ msgArg m om ∗ (msgArg m om -∗ P)))

instance raftLend_persistent (P : IProp GF) (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    Persistent (RaftLend P c r id s) := by
  unfold RaftLend; infer_instance

instance msgLend_persistent (P : IProp GF) (m : Loc) (om : Option MsgArg) :
    Persistent (MsgLend P m om) := by
  unfold MsgLend; infer_instance

/-- A nil `prop`. -/
theorem tracingPropsRep_nil : ⊢ tracingPropsRep (GF := GF) map.nil noProps := by
  unfold tracingPropsRep
  ileft
  isplitr <;> ipureintro
  · rfl
  · exact ⟨rfl, rfl, rfl⟩

/-- An empty, read-only `prop` (`traceSendMessage`'s map with no `Progress`). -/
theorem tracingPropsRep_empty (m : GoMap) :
    (m ↦$□ (∅ : GMap GoString GoInterface) : IProp GF) ⊢ tracingPropsRep m noProps := by
  iintro #Hm
  unfold tracingPropsRep
  iright
  iexists ∅, null
  iframe Hm
  isplitr
  · ipureintro
    simp [noProps]
  · simp only [noProps, tracingCCRep]; ipureintro; trivial

/-- `prop` with the sender's `match` and `next` (`traceSendMessage`'s map for a `MsgApp`). -/
theorem tracingPropsRep_mn (m : GoMap) (mt nx : w64) :
    (m ↦$□ (<[go!"next" := interface.mkOk go.uint64 #nx]>
        (<[go!"match" := interface.mkOk go.uint64 #mt]> (∅ : GMap GoString GoInterface))) : IProp GF) ⊢
      tracingPropsRep m { noProps with propMatch := some mt, propNext := some nx } := by
  iintro #Hm
  unfold tracingPropsRep
  iright
  iexists _, null
  iframe Hm
  have hnm : (go!"next" : GoString) ≠ go!"match" := by decide
  have hnc : (go!"next" : GoString) ≠ go!"cc" := by decide
  have hmc : (go!"match" : GoString) ≠ go!"cc" := by decide
  have hinj : ∀ a b : w64, (#a : val) = #b → a = b := fun a b h => go.IntoValInj.intoVal_inj h
  isplitr
  · ipureintro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [noProps]
    · intro _
      simp
    · intro w
      simp only [GMap.lookup_insert_ne _ _ hnm, GMap.lookup_insert]
      constructor
      · intro h; cases h; rfl
      · intro h
        have h' := (interface_mkOk_inj _ _ _ _).1 (Option.some.inj h)
        rw [hinj _ _ h'.2]
    · simp
    · intro w
      simp only [GMap.lookup_insert]
      constructor
      · intro h; cases h; rfl
      · intro h
        have h' := (interface_mkOk_inj _ _ _ _).1 (Option.some.inj h)
        rw [hinj _ _ h'.2]
    · simp
    · intro k hk
      have hk1 : k ≠ go!"next" := fun h => hk (by simp [h])
      have hk2 : k ≠ go!"match" := fun h => hk (by simp [h])
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk1), GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
      rfl
  · simp only [noProps, tracingCCRep]; ipureintro; trivial

/-- Raft's state held beside `X`. -/
theorem raftLend_sep (X : IProp GF) (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ RaftLend iprop(ownRaftPhysCV c c.voters r id s ∗ X) c r id s := by
  unfold RaftLend
  imodintro
  iintro ⟨Hp, HX⟩
  iframe Hp
  iintro Hp
  iframe Hp HX

/-- The message held beside `X`. -/
theorem msgLend_sep (X : IProp GF) (m : Loc) (om : Option MsgArg) :
    ⊢ MsgLend iprop(X ∗ msgArg m om) m om := by
  unfold MsgLend
  imodintro
  iintro ⟨HX, Hm⟩
  iframe Hm
  iintro Hm
  iframe HX Hm

/-- A message held beside `X`, at its fractions. -/
theorem msgLend_sep_some (X : IProp GF) (m : Loc) (a : MsgArg) :
    ⊢ MsgLend iprop(X ∗ msgPtsC m a.dq a.dqe a.cap a.ms) m (some a) :=
  msgLend_sep X m (some a)

/-- Raft's state alone. -/
theorem raftLend_self (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ RaftLend (ownRaftPhysCV (GF := GF) c c.voters r id s) c r id s := by
  unfold RaftLend
  imodintro
  iintro Hp
  iframe Hp
  iintro Hp
  iexact Hp

/-- (Q8 stage 1, slice 5) **A just-queued message, lent out of raft's state** (`NGhost.lq`,
`ownRaftPhysC_lq_lend`): what `raft.send` gives its hook, the message being queued by then. -/
theorem msgLend_lq (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (st : MsgSt)
    (h : (ml, st) ∈ s.gh.lq) :
    ⊢ MsgLend (ownRaftPhysCV (GF := GF) c c.voters r id s) ml
        (some ⟨DFrac.own 1, DFrac.discard, false, st⟩) := by
  unfold MsgLend
  imodintro
  iintro HP
  simp only [msgArg]
  iapply ownRaftPhysC_lq_lend c r id s ml st h $$ HP

/-- No message (nil). -/
theorem msgLend_nil (P : IProp GF) : ⊢ MsgLend P null none := by
  unfold MsgLend
  imodintro
  iintro HP
  simp only [msgArg]
  isplitr
  · ipureintro; trivial
  iintro -
  iexact HP

end defs

/-! ## The gates -/

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- (Q8 stage 1, slice 5) A fact needed only when traced, under the gate. -/
theorem trOwn_pure (tr : Option GName) (P : IProp GF) (φ : Prop) (h : tr ≠ none → φ) :
    trOwn tr P ⊢ trOwn tr iprop(P ∗ ⌜φ⌝) := by
  cases tr with
  | none => simp only [trOwn]; iintro -; iempintro
  | some γd =>
    simp only [trOwn]
    iintro HP
    iframe HP
    ipureintro; exact h (Option.some_ne_none γd)

/-- At a nil logger the optional gate gives `Q` whatever the mode. -/
theorem traceFireOpt_nil (tr : Option GName) (oE : Option (TraceEv → Prop)) (Q : IProp GF) :
    TraceFireOpt tr interface.nil oE Q ⊢ Q := by
  cases oE with
  | none => exact .rfl
  | some E => exact traceFire_nil tr E Q

/-- The optional gate for fewer events. -/
theorem traceFireOpt_mono_E (tr : Option GName) (tl : GoInterface) (oE oE' : Option (TraceEv → Prop))
    (Q : IProp GF) (h : oE = none ↔ oE' = none) (hE : ∀ E E', oE = some E → oE' = some E' → ∀ e, E' e → E e) :
    TraceFireOpt tr tl oE Q ⊢ TraceFireOpt tr tl oE' Q := by
  cases oE with
  | none =>
    cases oE' with
    | none => exact .rfl
    | some E' => exact absurd (h.1 rfl) (by simp)
  | some E =>
    cases oE' with
    | none => exact absurd (h.2 rfl) (by simp)
    | some E' => exact traceFire_mono_E tr tl E E' Q (hE E E' rfl rfl)


/-- (Q8 stage 1, slice 5) **A message hook's gate, the caller's** (`raft.send` takes it): as
`HookGate` (an update at `⊤`, run at the hook, giving the logger field and the gate `TraceFireOpt`
for the events `oE` the hook logs there), with the untraced nil logger (`tr = none → TraceLoggerOk`),
which `TraceFireOpt none tl none Q` does not say. -/
def HookGateOpt (tr : Option GName) (r : Loc) (oE : Option (TraceEv → Prop)) (Q : IProp GF) : IProp GF :=
  iprop(|={⊤}=> ∃ tl, r.[raft, go!"traceLogger"] ↦□ tl ∗ ⌜tr = none → TraceLoggerOk tl⌝ ∗
    TraceFireOpt tr tl oE Q)

/-- An untraced caller's gate: the struct's nil logger and `Q`. -/
theorem hookGateOpt_none (r : Loc) (oE : Option (TraceEv → Prop)) (tl : GoInterface) (Q : IProp GF)
    (hok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl ∗ Q : IProp GF) ⊢ HookGateOpt none r oE Q := by
  iintro ⟨#Htl, HQ⟩
  iunfold HookGateOpt
  imodintro
  iexists tl
  isplitr
  · iexact Htl
  isplitr
  · ipureintro; intro _; exact hok
  cases oE with
  | none => simp only [TraceFireOpt]; iexact HQ
  | some E =>
    simp only [TraceFireOpt, TraceFire]
    iframe HQ
    ipureintro; exact hok

end gates

end EtcdGrove
end Perennial
