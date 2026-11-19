/-
`fieldpath.Path.Equals`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Path__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
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

theorem fieldpath.Path.Equals.wp_proof
    (h_PathElement_Equals : fieldpath.PathElement.Equals.spec (GF := GF)) :
    fieldpath.Path.Equals.spec (GF := GF) := fun s s' dq dq' p p' => by
  wp_start as ⟨Hp, Hp'⟩
  unfold isPathF isPEs
  icases Hp with ⟨%es, Hs, #Hl⟩
  icases Hp' with ⟨%es', Hs', #Hl'⟩
  ihave %hl := ownSlice_len _ _ _ $$ Hs
  ihave %hl' := ownSlice_len _ _ _ $$ Hs'
  ihave %hp := fpL.isPEL_length _ _ $$ Hl
  ihave %hp' := fpL.isPEL_length _ _ $$ Hl'
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ
    isplitl [Hs]
    · iexists es; iframe; iexact Hl
    isplitl [Hs']
    · iexists es'; iframe; iexact Hl'
    ipureintro; simp only [Bool.false_eq_true, false_iff]; intro h; subst h; apply Hif; word
  have hlenEq : s.len = s'.len := Hif
  have hlen : es.length = es'.length := by rw [hl.1, hl'.1, Hif]
  rename_i ivar_ptr
  irename : (ivar_ptr ↦ zero_val w64 : IProp GF) => Hiv
  ihave HI : (∃ j k : w64, "i" ∷ i_ptr ↦ j ∗ "Hiv" ∷ ivar_ptr ↦ k ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
      p.take (sint.nat j) = p'.take (sint.nat j)⌝ : IProp GF) $$ [i Hiv]
  · iexists _, _; iframe; ipureintro; simp only [sint.nat]; refine ⟨by word, by word, ?_⟩; simp
  wp_for HI
  wp_if_destruct
  · obtain ⟨hj0, hjl, htake⟩ := Hj
    have hjn : sint.nat j < es.length := by rw [hl.1]; word
    have hjn' : sint.nat j < es'.length := by omega
    simp only [hj0, Hif, _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat j) as x
    list_elem es' (sint.nat j) as x'
    wp_apply (wp_load_slice_index s (sint.Z j) es dq x hj0) $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have hc' : sint.Z j < sint.Z s'.len := by rw [← hlenEq]; exact Hif
    simp only [hj0, hc', _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index s' (sint.Z j) es' dq' x' hj0) $$ [Hs'] as Hs'
    · iframe; ipureintro; exact Hx'_lookup
    simp only [hj0, Hif, _root_.and_self, ↓reduceIte]
    wp_pures; wp_method_call; wp_call
    wp_apply (wp_load_slice_index s (sint.Z j) es dq x hj0) $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    ihave ⟨%pe, %hpe, #Hpe⟩ := fpL.isPEL_lookup es p (sint.nat j) x Hx_lookup $$ Hl
    ihave ⟨%pe', %hpe', #Hpe'⟩ := fpL.isPEL_lookup es' p' (sint.nat j) x' Hx'_lookup $$ Hl'
    wp_apply (h_PathElement_Equals x x' pe pe') $$ [$Hpe $Hpe'] as %r %hr
    have hq : p[sint.nat j]? = p'[sint.nat j]? → p.take (sint.nat j + 1) = p'.take (sint.nat j + 1) := by
      intro h; rw [List.take_add_one, List.take_add_one, htake, h]
    cases r <;> wp_auto
    · wp_for_post
      iapply HΦ
      isplitl [Hs]
      · iexists es; iframe; iexact Hl
      isplitl [Hs']
      · iexists es'; iframe; iexact Hl'
      ipureintro
      simp only [Bool.false_eq_true, false_iff]
      intro h; subst h
      rw [hpe] at hpe'; cases hpe'
      simp at hr
    · wp_for_post
      iframe
      iexists j + 1, j
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (j + 1) = sint.nat j + 1 by word]
      apply hq
      rw [hpe, hpe', (hr.1 rfl)]
  · iapply HΦ
    isplitl [Hs]
    · iexists es; iframe; iexact Hl
    isplitl [Hs']
    · iexists es'; iframe; iexact Hl'
    ipureintro
    simp only [_root_.true_iff]
    have : sint.nat j = p.length := by rw [← hp, hl.1]; word
    rw [this, List.take_length, show p.length = p'.length by omega, List.take_length] at Hj
    exact Hj.2.2

end proof

end smd
end EtcdGrove
end Perennial
