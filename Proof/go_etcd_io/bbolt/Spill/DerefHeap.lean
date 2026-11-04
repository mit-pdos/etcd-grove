/-
The writer's heap under `dereference` (U9b, `notes/bbolt-proof-plan.md`): `wtxW` opened to its
heap, its view's cells and its statistics' token (and closed on a heap of the same view, handles
and registry), and the heap's facts kept by a `derefStep`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefRel
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance BC.core_persistent' (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

/-- **`wtxW`, opened**: its heap, its view's cells and its statistics' token; it closes on any heap
`X'` of the same view, handles and node registry. -/
theorem wtxW_open (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r ∗
      wtxHeap tx (DFrac.own 1) X ∗ viewCells wq X.v ∗ statsTok r m 1 ∗
      (∀ X', ⌜X'.v = X.v ∧ X'.handles = X.handles ∧ X'.nloc = X.nloc⌝ -∗
        wtxHeap tx (DFrac.own 1) X' -∗ viewCells wq X.v -∗ statsTok r m 1 -∗ wtxW K tx r m X') := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpk, #Hcore, %Hr, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hv, Hmap⟩
  iframe Hh Hv Hst
  isplitr
  · iexact Hpk
  isplitr
  · iexact Hcore
  isplitr
  · iexact Hreg
  iintro %X' %He Hh Hv Hst
  obtain ⟨hv, hh, hn⟩ := He
  rw [hv, hh, hn]
  iframe
  isplitr
  · iexact Hpk
  isplitr
  · iexact Hcore
  isplitr
  · ipureintro; exact Hr
  iexact Hreg

/-- The heap's facts are kept by a `derefStep` (no object moves, no bucket or parent changes). -/
theorem heapOK_step (tx : Loc) (X X' : WX) (h : derefStep X X') (hok : heapOK (GF := GF) tx X) :
    heapOK (GF := GF) tx X' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  have hbs := derefStep_bs h
  refine ⟨by rw [h.2.2.2.2.1]; exact h1, objsDisj_step h h2, ?_, ?_, ?_⟩
  · intro bl B' hB'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    rw [(bktStep_fields hs).1]; exact h3 bl B hB
  · intro bl B' n r' hB' hr'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨r, hr, hrs⟩ := optRel_some_r (hr' ▸ hs.2 n)
    rw [(nodeStep_nv hrs).1]; exact h4 bl B n r hB hr
  · intro n y hn
    rw [h.2.2.2.1] at hn
    rw [objs_isSome_step h h2]; exact h5 n y hn

end heap

end bbolt
end EtcdGrove
end Perennial
