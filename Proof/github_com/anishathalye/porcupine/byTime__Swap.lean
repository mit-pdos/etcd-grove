/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/byTime__Swap.lean`. -/
module

public import Spec.github_com.anishathalye.porcupine.byTime__Swap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem byTime.Swap.wp_proof : byTime.Swap.spec (GF := GF) (hG := hG) :=
  fun sl es i j a b => by
  wp_start as ⟨Hs, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < es.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < es.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
    have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
    have := Hl.1; refine ⟨hj0, ?_⟩; word
  try simp only [Hbi, _root_.and_self, ite_true]
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) es (DFrac.own 1) b hj0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hb
  (try wp_auto)
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) es (DFrac.own 1) a hi0 $$ [Hs] as Hs
  · iframe; ipureintro; exact ha
  (try wp_auto)
  wp_apply wp_store_slice_index sl (sint.Z i) es b $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hi0, by have := Hl.1; word⟩
  (try wp_auto)
  wp_apply wp_store_slice_index sl (sint.Z j) _ a $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hj0, by simp only [List.length_set]; have := Hl.1; word⟩
  (try wp_auto)
  iapply HΦ
  iexact Hs

end proof

end porcupine
end EtcdGrove
end Perennial
