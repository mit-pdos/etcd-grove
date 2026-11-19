/-
`fieldpath.MakePath`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.MakePath.wp_proof :
    fieldpath.MakePath.spec (GF := GF) := fun s dq is es p => by
  wp_start as ⟨Hs, #Hp, %His⟩
  ihave %hl := ownSlice_len _ _ _ $$ Hs
  ihave %hpl := isPEs_length_law_holds _ _ $$ Hp
  have hil : is.length = es.length := by rw [His, List.length_map]
  wp_auto
  ihave Hnil := ownSlice_nil (V := fieldpath.PathElement) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := fieldpath.PathElement)
  irename : (p_ptr ↦ GoInterface.nil : IProp GF) => Hpv
  ihave HI : (∃ (j : w64) (sl : GoSlice) (v : GoInterface), "i" ∷ i_ptr ↦ j ∗ "fp" ∷ fp_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* es.take (sint.nat j) ∗ "Hcap" ∷ ownSliceCap fieldpath.PathElement sl (DFrac.own 1) ∗
      "Hpv" ∷ p_ptr ↦ v ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF)
      $$ [i fp Hnil Hcap Hpv]
  · iexists (W64 0), slice.nil, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl; iexact Hnil; isplitl; iexact Hcap
    ipureintro; word
  wp_for HI
  by_cases hc : sint.Z j < sint.Z s.len
  · wp_if_destruct <;> try (exfalso; simp_all; done)
    have hjn : sint.nat j < is.length := by rw [hl.1]; word
    simp only [Hj.1, hc, _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat j) as e
    have hie : is[sint.nat j]? = some (interface.mkOk fieldpath.PathElement.ty #e) := by
      rw [His, List.getElem?_map, He_lookup]; rfl
    wp_apply (wp_load_slice_index s (sint.Z j) is dq _ Hj.1) $$ [Hs] as Hs
    · iframe; ipureintro; exact hie
    simp only [↓reduceIte, decide_true]
    wp_auto
    wp_apply (wp_slice_literal (V := fieldpath.PathElement) [e])
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_auto
    wp_apply (wp_slice_append sl _ _ [e] (DFrac.own 1)) $$ [$Hsl $Hcap $Hosl] as %sl' ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists j + 1, sl', _
    iframe
    rw [show sint.nat (j + 1) = sint.nat j + 1 by word, List.take_add_one, He_lookup]
    iframe
    ipureintro; word
  · wp_if_destruct <;> try (exfalso; simp_all; done)
    have hje : sint.nat j = es.length := by rw [← hil, hl.1]; word
    rw [hje, List.take_length]
    iapply HΦ
    iframe
    isplitr
    · ipureintro; rfl
    unfold isPathF
    iexists es; iframe; iexact Hp

end proof

end smd
end EtcdGrove
end Perennial
