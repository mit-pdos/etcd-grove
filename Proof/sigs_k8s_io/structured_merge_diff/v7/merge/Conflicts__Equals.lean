/-
`merge.Conflicts.Equals`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Conflict__Equals
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist

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
variable [package_sem : merge.Assumptions]

private theorem isConflictL_length : ∀ (xs : List merge.Conflict) (cs : List (GoString × Path)),
    isConflictL (GF := GF) xs cs ⊢ ⌜xs.length = cs.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold isConflictL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isConflictL; iintro %h; exact h.elim
  | x :: xs, (m, p) :: cs => by
      unfold isConflictL
      iintro ⟨_, _, H⟩
      ihave %h := isConflictL_length xs cs $$ H
      ipureintro; simp [h]

private theorem isConflictL_lookup : ∀ (xs : List merge.Conflict) (cs : List (GoString × Path))
    (i : Nat) (x : merge.Conflict), xs[i]? = some x →
    isConflictL (GF := GF) xs cs ⊢ ∃ c, ⌜cs[i]? = some c⌝ ∗ isConflict x c
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold isConflictL; iintro %h; exact h.elim
  | y :: xs, (m, p) :: cs, 0, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      unfold isConflictL isConflict
      iintro ⟨%hm, Hp, _⟩
      iexists (m, p)
      iframe Hp
      ipureintro; exact ⟨rfl, hm⟩
  | y :: xs, (m, p) :: cs, i + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      unfold isConflictL
      iintro ⟨_, _, H⟩
      ihave ⟨%c, %hc, Hc⟩ := isConflictL_lookup xs cs i x h $$ H
      iexists c
      iframe Hc
      ipureintro; simpa using hc

theorem merge.Conflicts.Equals.wp_proof
    (h_Conflict_Equals : merge.Conflict.Equals.spec (GF := GF)) :
    merge.Conflicts.Equals.spec (GF := GF) := fun s s' a b => by
  wp_start as ⟨Hp, Hp'⟩
  unfold isConflicts
  icases Hp with ⟨%es, Hs, #Hl⟩
  icases Hp' with ⟨%es', Hs', #Hl'⟩
  ihave %hl := ownSlice_len _ _ _ $$ Hs
  ihave %hl' := ownSlice_len _ _ _ $$ Hs'
  ihave %hp := isConflictL_length _ _ $$ Hl
  ihave %hp' := isConflictL_length _ _ $$ Hl'
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ
    ipureintro; simp only [Bool.false_eq_true, false_iff]; intro h; subst h; apply Hif; word
  have hlenEq : s.len = s'.len := Hif
  have hlen : es.length = es'.length := by rw [hl.1, hl'.1, Hif]
  rename_i ivar_ptr
  irename : (ivar_ptr ↦ zero_val w64 : IProp GF) => Hiv
  ihave HI : (∃ j k : w64, "i" ∷ i_ptr ↦ j ∗ "Hiv" ∷ ivar_ptr ↦ k ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
      a.take (sint.nat j) = b.take (sint.nat j)⌝ : IProp GF) $$ [i Hiv]
  · iexists _, _; iframe; ipureintro; simp only [sint.nat]; refine ⟨by word, by word, ?_⟩; simp
  wp_for HI
  wp_if_destruct
  · obtain ⟨hj0, hjl, htake⟩ := Hj
    have hjn : sint.nat j < es.length := by rw [hl.1]; word
    have hjn' : sint.nat j < es'.length := by rw [hl'.1, ← hlenEq]; word
    simp only [hj0, Hif, _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat j) as x
    list_elem es' (sint.nat j) as x'
    wp_apply (wp_load_slice_index s (sint.Z j) es DFrac.discard x hj0) $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have hc' : sint.Z j < sint.Z s'.len := by rw [← hlenEq]; exact Hif
    simp only [hj0, hc', _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index s' (sint.Z j) es' DFrac.discard x' hj0) $$ [Hs'] as Hs'
    · iframe; ipureintro; exact Hx'_lookup
    simp only [hj0, Hif, _root_.and_self, ↓reduceIte]
    wp_pures; wp_method_call; wp_call
    wp_apply (wp_load_slice_index s (sint.Z j) es DFrac.discard x hj0) $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    ihave ⟨%pe, %hpe, #Hpe⟩ := isConflictL_lookup es a (sint.nat j) x Hx_lookup $$ Hl
    ihave ⟨%pe', %hpe', #Hpe'⟩ := isConflictL_lookup es' b (sint.nat j) x' Hx'_lookup $$ Hl'
    wp_apply (h_Conflict_Equals x x' pe pe') $$ [$Hpe $Hpe'] as %r %hr
    have hq : a[sint.nat j]? = b[sint.nat j]? → a.take (sint.nat j + 1) = b.take (sint.nat j + 1) := by
      intro h; rw [List.take_add_one, List.take_add_one, htake, h]
    cases r <;> wp_auto
    · wp_for_post
      iapply HΦ
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
    ipureintro
    simp only [_root_.true_iff]
    have : sint.nat j = a.length := by rw [← hp, hl.1]; word
    rw [this, List.take_length, show a.length = b.length by omega, List.take_length] at Hj
    exact Hj.2.2

end proof

end smd
end EtcdGrove
end Perennial
