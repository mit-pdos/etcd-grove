/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__IsSortOptionValid.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__IsSortOptionValid

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

theorem Op.IsSortOptionValid.wp_proof : Op.IsSortOptionValid.spec (GF := GF) (hG := hG) := by
  intro opv o
  wp_start as ⟨#Hat, #Hmaps⟩
  iunfold opFullAt at Hat
  icases Hat with ⟨Hat, -, -, -, #Hsort⟩
  iunfold opAt at Hat
  icases Hat with ⟨%Hf, -⟩
  unfold OpFields at Hf
  obtain ⟨-, -, hs, -⟩ := Hf
  wp_auto
  cases hss : o.base.sortSet
  · have hs' : opv.sort' = null := Classical.byContradiction fun hne => by
      rw [hss] at hs; exact absurd (hs.1 hne) (by simp)
    rw [hs']
    wp_auto
    have : sortValid o = true := by simp [sortValid, hss]
    rw [this]
    iapply HΦ
    itrivial
  · have hs' : opv.sort' ≠ null := fun h => by
      rw [hss] at hs; exact hs.2 rfl h
    iunfold opSortAt at Hsort
    rw [hss]
    simp only [↓reduceIte]
    simp only [sortNamesIf, ↓reduceIte]
    iunfold sortNamesOk at Hmaps
    icases Hmaps with ⟨-, ⟨%mo, %Mo, #Hmo, #Hmos, %HMo⟩, ⟨%mt, %Mt, #Hmt, #Hmts, %HMt⟩⟩
    rw [decide_eq_false hs']
    iStructNamed Hsort
    wp_auto
    have hwo : sortOrderWire o = W32 (sint.Z o.sortOrder) := by simp [sortOrderWire, hss]
    have hwt : sortTargetWire o = W32 (sint.Z o.sortTarget) := by simp [sortTargetWire, hss]
    wp_apply (wp_map_lookup2 _ _ mo Mo (W32 (sint.Z o.sortOrder)) DFrac.discard) $$ [$Hmos]
    iintro -
    wp_auto
    wp_if_destruct
    rotate_left
    · have ho : ¬ (0 ≤ sint.Z (sortOrderWire o) ∧ sint.Z (sortOrderWire o) ≤ 2) := by
        rw [hwo]; exact fun h => Hif ((HMo _).2 h)
      have : sortValid o = false := by simp [sortValid, hss, ho]
      rw [this]
      iapply HΦ; itrivial
    have ho : 0 ≤ sint.Z (sortOrderWire o) ∧ sint.Z (sortOrderWire o) ≤ 2 := by
      rw [hwo]; exact (HMo _).1 Hif
    wp_apply (wp_map_lookup2 _ _ mt Mt (W32 (sint.Z o.sortTarget)) DFrac.discard) $$ [$Hmts]
    iintro -
    wp_auto
    wp_if_destruct
    rotate_left
    · have ht : ¬ (0 ≤ sint.Z (sortTargetWire o) ∧ sint.Z (sortTargetWire o) ≤ 4) := by
        rw [hwt]; exact fun h => Hif ((HMt _).2 h)
      have : sortValid o = false := by simp [sortValid, hss, ht]
      rw [this]
      iapply HΦ; itrivial
    have ht : 0 ≤ sint.Z (sortTargetWire o) ∧ sint.Z (sortTargetWire o) ≤ 4 := by
      rw [hwt]; exact (HMt _).1 Hif
    have : sortValid o = true := by simp [sortValid, hss, ho, ht]
    rw [this]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
