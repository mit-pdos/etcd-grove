/-
The writer's heap under `dereference` (U9b, `notes/bbolt-proof-plan.md`): `wtxW` opened to its
heap, its view's cells and its statistics' token (and closed on a heap of the same view, handles
and registry), and the heap's facts kept by a `derefStep`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefModel
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
  obtain ⟨-, -, -, -, hrl, -, -, -, -, -, hbs⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hok
  refine ⟨by rw [hrl]; exact h1, ?_, ?_, ?_⟩
  · intro bl B' hB' n hn
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    have hn' : (B.ns !! n).isSome := by
      have := hs.2 n
      revert this hn
      cases B.ns !! n <;> cases B'.ns !! n <;> simp [optRel]
    obtain ⟨hnb, hno⟩ := h2 bl B hB n hn'
    refine ⟨?_, ?_⟩
    · have := hbs n; rw [hnb] at this; exact optRel_none_l this
    · intro bl2 B2' hB2' hne
      obtain ⟨B2, hB2, hs2⟩ := optRel_some_r (hB2' ▸ hbs bl2)
      have := hs2.2 n; rw [hno bl2 B2 hB2 hne] at this; exact optRel_none_l this
  · intro bl B' hB'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    rw [(bktStep_fields hs).1]; exact h3 bl B hB
  · intro bl B' n r' hB' hr'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨r, hr, hrs⟩ := optRel_some_r (hr' ▸ hs.2 n)
    rw [(nodeStep_nv hrs).1]; exact h4 bl B n r hB hr

end heap

end bbolt
end EtcdGrove
end Perennial
