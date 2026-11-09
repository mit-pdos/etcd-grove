/-
**The objects a `Ready` hands out** (raft-entsize §2 step 3, 2026-11-09).

- `snapUf l st`: a `MsgSnap`'s top-level unknown fields are none (persistent): the `pbMsg` of the
  literal `maybeSendSnapshot` builds (`msgOwn_lit_uf`), which `raft.send` takes and the outbox keeps
  beside the message (`msgQ`), so that the content a `Ready` hands out can pin them
  (`msgPtsC_msgPtsCC_uf`: a message's content form may take its `pbMsg` from anywhere).
- `outObjR γ m c`, `outEntR γ e c`: persistent elements of the cluster's monotone set of the objects
  handed out (`RaftNames.out`, its authority in `raftOutInv`, part of the commit invariant), at the
  content they were handed out with. A message's element is keyed by its own fields and its
  responses' pointers (`outKey`): what the size law reads of it (`msgSizeOk` requires no responses).
  Raft's `Ready` proofs insert them (`raftOutInv_insert`, internal, `MsgOutIns.lean`).
- `msgOutR γ l dq st`: a message handed out at `dq` holding `st`, at a content `c` raft pinned
  (`sentOk`: its snapshot's conf state without unknown fields, a `MsgSnap` without top-level unknown
  fields), with its element `outObjR γ l c`.
-/
module

public import Proof.go_etcd_io.raft.v3.PbContentOwn
public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Countable contents (the set's keys) -/

section countable
variable [GooseExts]

instance EntryC.countable : Pos.Countable EntryC :=
  .ofInjective (fun c => Pos.Countable.encode (c.term, c.index, c.type, c.data, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl)

instance CSC.countable : Pos.Countable CSC :=
  .ofInjective (fun c => Pos.Countable.encode
      (c.voters, c.learners, c.votersOutgoing, c.learnersNext, c.autoLeave, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl)

instance SnapMetaC.countable : Pos.Countable SnapMetaC :=
  .ofInjective (fun c => Pos.Countable.encode (c.confState, c.index, c.term, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl)

instance SnapC.countable : Pos.Countable SnapC :=
  .ofInjective (fun c => Pos.Countable.encode (c.data, c.metadata, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl)

instance MsgFC.countable : Pos.Countable MsgFC :=
  .ofInjective (fun c => Pos.Countable.encode
      ((c.type, c.to, c.frm, c.term, c.logTerm, c.index, c.entries),
       (c.commit, c.vote, c.snapshot, c.reject, c.rejectHint, c.context, c.uf)))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ := h
      rfl)

/-- **The handed-out set's key** of an object and its content: a message's own fields and its
responses' pointers (what the size law reads of it: `msgSizeOk` requires no responses, and reads
only the message's own fields), an entry's content. -/
def outKey : Sum (Loc × MsgC) (Loc × EntryC) → Sum (Loc × MsgFC × List Loc) (Loc × EntryC)
  | .inl (m, c) => .inl (m, c.f, c.resps.map Prod.fst)
  | .inr x => .inr x

end countable

/-! ## The predicates -/

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A `MsgSnap`'s top-level unknown fields are none** (persistent; `emp`-like for any other type):
the `pbMsg` of the literal `maybeSendSnapshot` builds. -/
def snapUfT (l : Loc) (ty : w32) : IProp GF :=
  iprop(⌜ty ≠ MsgSnap⌝ ∨ pbMsg raftpb.Message l [])

instance snapUfT_persistent (l : Loc) (ty : w32) : Persistent (snapUfT (GF := GF) l ty) := by
  unfold snapUfT; infer_instance

/-- `snapUfT` at a message's type. -/
abbrev snapUf (l : Loc) (st : MsgSt) : IProp GF := snapUfT l st.msg.Type'

/-- **An element of the handed-out set** (persistent): the object and content `x`, by its key. -/
def outSetR (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) : IProp GF :=
  ghostMapElem γ.out (Pos.Countable.encode (outKey x)) DFrac.discard ()

instance outSetR_persistent (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) :
    Persistent (outSetR (GF := GF) γ x) := by
  unfold outSetR; infer_instance

/-- The message `m` was handed out at the content `c`. -/
abbrev outObjR (γ : RaftNames) (m : Loc) (c : MsgC) : IProp GF := outSetR γ (.inl (m, c))

/-- The entry `e` was handed out at the content `c`. -/
abbrev outEntR (γ : RaftNames) (e : Loc) (c : EntryC) : IProp GF := outSetR γ (.inr (e, c))

theorem snapUfT_ne (l : Loc) (ty : w32) (h : ty ≠ MsgSnap) : ⊢ snapUfT (GF := GF) l ty := by
  unfold snapUfT; ileft; ipureintro; exact h

/-- `snapUf` reads only the type. -/
theorem snapUf_congr (l : Loc) (st st' : MsgSt) (h : st'.msg.Type' = st.msg.Type') :
    snapUf (GF := GF) l st ⊢ snapUf l st' := by
  unfold snapUf; rw [h]

end generic

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What raft pins of a message's content**: its snapshot's conf state, if any, without unknown
fields (as `msgPtsC` holds it, `csUfNil`), and a `MsgSnap` without top-level unknown fields (the
literal `maybeSendSnapshot` builds). -/
def MsgC.sentOk (c : MsgC) : Prop := c.csUfNil ∧ (c.f.msgM.Type' = MsgSnap → c.f.uf = [])

/-- **A message handed out**, owned at `dq` (its entries and `Context` frozen, no capacity: as
`msgOwn`), holding `st`, at the content `c` raft pinned (`sentOk`), with its element of the
handed-out set. -/
def msgOutR (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ ⌜c.model = st ∧ c.sentOk⌝ ∗ outObjR γ l c)

end defs

/-! ## Laws -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A message's content form may take its `pbMsg` from anywhere**: today's message with a `pbMsg`
of its object at `uf0` is an object at a content whose own unknown fields are `uf0`. -/
theorem msgPtsC_msgPtsCC_uf (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (uf0 : List w8) :
    msgPtsC (GF := GF) l dq dqe cap st ∗ pbMsg raftpb.Message l uf0 ⊢
      ∃ c : MsgC, msgPtsCC l dq dqe cap c ∗ ⌜c.model = st ∧ c.csUfNil ∧ c.f.uf = uf0⌝ := by
  iintro ⟨H, #Hp⟩
  icases msgPtsC_msgPtsCC l dq dqe cap st $$ H with ⟨%c, Hc, %Hm⟩
  obtain ⟨Hmod, Hcs⟩ := Hm
  iexists MsgC.mk { c.f with uf := uf0 } c.resps
  isplitl [Hc]
  · unfold msgPtsCC
    icases Hc with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
      %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
      HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, -⟩
    simp only [MsgC.f, MsgC.resps]
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hp
  · ipureintro
    refine ⟨?_, ?_, rfl⟩
    · rw [← Hmod]; cases c; rfl
    · cases c; exact Hcs

/-- A handed-out message is owned as today's `msgOwn`. -/
theorem msgOutR_msgOwn (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOutR (GF := GF) γ l dq st ⊢ msgOwn l dq st := by
  unfold msgOutR
  iintro ⟨%c, Hc, %Hm, -⟩
  obtain ⟨Hmod, Hok, -⟩ := Hm
  rw [← Hmod]
  simp only [msgOwn, msgPts]
  iapply msgPtsCC_msgPtsC l dq DFrac.discard false c Hok $$ Hc

/-- **The `MsgSnap` law**: a handed-out `MsgSnap` has no top-level unknown fields. -/
theorem msgOutR_snap (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOutR (GF := GF) γ l dq st ⊢
      ∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ outObjR γ l c ∗
        ⌜c.model = st ∧ c.csUfNil ∧ (st.msg.Type' = MsgSnap → c.f.uf = [])⌝ := by
  unfold msgOutR
  iintro ⟨%c, Hc, %Hm, #Ho⟩
  obtain ⟨Hmod, Hcs, Hsn⟩ := Hm
  iexists c
  iframe Hc Ho
  ipureintro
  refine ⟨Hmod, Hcs, fun h => Hsn ?_⟩
  rw [← Hmod] at h; exact h

/-- An owned message with its `snapUf` is an object at a content raft pins (`sentOk`). -/
theorem msgOwn_snapUf_CC (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwn (GF := GF) l dq st ∗ snapUf l st ⊢
      ∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ ⌜c.model = st ∧ c.sentOk⌝ := by
  iintro ⟨H, Hu⟩
  unfold snapUf snapUfT
  icases Hu with (%Hne | #Hp)
  · simp only [msgOwn, msgPts]
    icases msgPtsC_msgPtsCC l dq DFrac.discard false st $$ H with ⟨%c, Hc, %Hm⟩
    iexists c
    iframe Hc
    ipureintro
    refine ⟨Hm.1, Hm.2, fun h => absurd (by rw [← Hm.1]; exact h) Hne⟩
  · simp only [msgOwn, msgPts]
    icases msgPtsC_msgPtsCC_uf l dq DFrac.discard false st [] $$ [H Hp] with ⟨%c, Hc, %Hm⟩
    · iframe H Hp
    iexists c
    iframe Hc
    ipureintro
    exact ⟨Hm.1, Hm.2.1, fun _ => Hm.2.2⟩

end lemmas

end EtcdGrove
end Perennial
