/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__toRangeRequest.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__toRangeRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.toRangeRequest.wp_proof : Op.toRangeRequest.spec (GF := GF) (hG := hG) := by
  intro opv o
  wp_start as ⟨#Hat, %Ht⟩
  iunfold opFullAt at Hat
  icases Hat with ⟨Hat, #Hkey, %Hf2, -, #Hsort⟩
  iunfold opAt at Hat
  icases Hat with ⟨%Hf, #Hend⟩
  unfold OpFields at Hf
  obtain ⟨hc, -, hs, hl, hmin, hmax, hcmin, hcmax, -, -, -, -, hrev, hser, -⟩ := Hf
  obtain ⟨ht, hko, -⟩ := Hf2
  wp_auto
  rw [ht, Ht]
  wp_auto
  cases hss : o.base.sortSet
  · have hs' : opv.sort' = null := Classical.byContradiction fun hne => by
      rw [hss] at hs; exact absurd (hs.1 hne) (by simp)
    rw [hs']
    wp_auto
    iapply HΦ
    iexists _
    iframe
    isplitl []
    · iexact Hkey
    isplitl []
    · iexact Hend
    ipureintro
    simp only [rangeReqOp, rangeWireOf, sortOrderWire, sortTargetWire, hss, hl, hrev, hser, hko, hc,
      hmin, hmax, hcmin, hcmax]
    rfl
  · have hs' : opv.sort' ≠ null := fun h => by
      rw [hss] at hs; exact hs.2 rfl h
    iunfold opSortAt at Hsort
    rw [hss]
    simp only [↓reduceIte]
    rw [decide_eq_false hs']
    iStructNamed Hsort
    wp_auto
    iapply HΦ
    iexists _
    iframe
    isplitl []
    · iexact Hkey
    isplitl []
    · iexact Hend
    ipureintro
    simp only [rangeReqOp, rangeWireOf, sortOrderWire, sortTargetWire, hss, hl, hrev, hser, hko, hc,
      hmin, hmax, hcmin, hcmax, ↓reduceIte]

end proof

end EtcdGrove
end Perennial
