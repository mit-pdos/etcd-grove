/-
U8's shared lemmas (`notes/bbolt-proof-plan.md`): the view's cells split by fraction, and a kept
slice's bytes read through its source (`srcOwn`: the view's cells, or persistent heap bytes).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section base
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `srcOwn_persistent`: `Inv/WtxHeap` (batch 18).

omit hos [GooseSemantics] go_gctx sem in
/-- The view's cells split by fraction. -/
theorem viewCells_split (q1 q2 : Qp) (v : View) :
    viewCells (GF := GF) (q1 + q2) v ⊣⊢ viewCells q1 v ∗ viewCells q2 v := by
  unfold viewCells
  rw [← BigSepM.bigSepM_sep_eq]
  constructor
  · apply BigSepM.bigSepM_mono_of_forall
    intro k x
    exact ((bytesPointsto_dfractional (GF := GF) _ x).dfractional (DFrac.own q1) (DFrac.own q2)).1
  · apply BigSepM.bigSepM_mono_of_forall
    intro k x
    exact ((bytesPointsto_dfractional (GF := GF) _ x).dfractional (DFrac.own q1) (DFrac.own q2)).2

omit hos [GooseSemantics] go_gctx sem in
/-- The view's cells in two halves. -/
theorem viewCells_halves (q : Qp) (v : View) :
    viewCells (GF := GF) q v ⊣⊢ viewCells q.half v ∗ viewCells q.half v := by
  have h := viewCells_split (GF := GF) q.half q.half v
  rw [Qp.half_add_half] at h
  exact h

/-- **A kept slice's bytes, read** (not stale): through the view's cells for a view source, the
persistent bytes for a heap one; and back. The view's base is positive (`mapFields`; batch 21:
`viewCells_slices_acc` needs it for an empty slice). -/
theorem srcOwn_acc (q : Qp) (v : View) (s : GoSlice) (src : Src) (bs : List w8)
    (hs : src ≠ Src.stale) (hb : 0 < v.base.addr) :
    srcOwn (GF := GF) v s src bs ∗ viewCells q v ⊢ ∃ dq : DFrac, s ↦*{dq} bs ∗
      (s ↦*{dq} bs -∗ srcOwn v s src bs ∗ viewCells q v) := by
  cases src with
  | stale => exact absurd rfl hs
  | own dq0 =>
    unfold srcOwn
    iintro ⟨#Hs, Hv⟩
    iexists DFrac.discard
    iframe Hs
    iintro _
    iframe Hv
  | view =>
    unfold srcOwn
    iintro ⟨%Hin, Hv⟩
    icases viewCells_slices_acc q v [(s, bs)] hb (by simpa using Hin) $$ Hv with ⟨%dq, Hs, Hback⟩
    iexists dq
    ihave Hs := BigSepL.bigSepL_singleton.1 $$ Hs
    iframe Hs
    iintro Hs
    isplitr
    · ipureintro; exact Hin
    iapply Hback
    iapply BigSepL.bigSepL_singleton.2
    iexact Hs

end base

end bbolt
end EtcdGrove
end Perennial
