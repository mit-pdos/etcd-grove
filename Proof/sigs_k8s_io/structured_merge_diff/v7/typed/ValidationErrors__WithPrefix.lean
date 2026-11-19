/-
`typed.ValidationErrors.WithPrefix`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithPrefix

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
variable [package_sem : typed.Assumptions]

theorem typed.ValidationErrors.WithPrefix.wp_proof :
    typed.ValidationErrors.WithPrefix.spec (GF := GF) := fun errs es pfx => by
  wp_start as Hs
  wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  irename : (prefix_ptr ↦ pfx : IProp GF) => Hpfx
  ihave %Hlen := ownSlice_len $$ Hs
  let f : typed.ValidationError → typed.ValidationError := fun e => { e with Path' := pfx ++ e.Path' }
  ihave IH : iprop(∃ (n k : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Higo" ∷ igo ↦ k ∗
      "Hs" ∷ errs ↦* ((es.take (sint.nat n)).map f ++ es.drop (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ es.length⌝) $$ [i Higo Hs]
  · iexists W64 0, _
    iframe i Higo
    isplitl [Hs]
    · rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.drop_zero, List.map_nil, List.nil_append]; iexact Hs
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < es.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z errs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, es[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have He' : (List.map f (List.take (sint.nat n) es) ++ List.drop (sint.nat n) es)[(sint.Z n).toNat]? = some e := by
      rw [show (sint.Z n).toNat = sint.nat n from rfl, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_take, show min (sint.nat n) es.length = sint.nat n by omega,
        Nat.sub_self, List.getElem?_drop, Nat.add_zero, He]
    icases ownSlice_elem_acc (sint.Z n) e errs _ _ Hn.1 He' $$ Hs with ⟨He, Hs⟩
    wp_auto
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_auto
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_auto
    ihave Hs := Hs $$ He
    wp_for_post
    iframe
    iexists n + W64 1, n
    iframe i Higo
    isplitl [Hs]
    · have Hset : (List.map f (List.take (sint.nat n) es) ++ List.drop (sint.nat n) es).set (sint.Z n).toNat
          ({ Path' := pfx ++ e.Path', ErrorMessage' := e.ErrorMessage' } : typed.ValidationError) = List.map f (List.take (sint.nat (n + W64 1)) es) ++ List.drop (sint.nat (n + W64 1)) es := by
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, show (sint.Z n).toNat = sint.nat n from rfl]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set]
        simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
        rcases Nat.lt_trichotomy j (sint.nat n) with hj | hj | hj
        · rw [if_neg (by omega), List.getElem?_append_left (by simp; omega),
            List.getElem?_append_left (by simp; omega)]
          simp only [List.getElem?_map, List.getElem?_take]
          rw [if_pos hj, if_pos (by omega)]
        · subst hj
          rw [if_pos rfl, if_pos (by omega), List.getElem?_append_left (by simp; omega)]
          simp only [List.getElem?_map, List.getElem?_take, show sint.nat n < sint.nat n + 1 by omega,
            ↓reduceIte, He]
          rfl
        · rw [if_neg (by omega), List.getElem?_append_right (by simp; omega),
            List.getElem?_append_right (by simp; omega)]
          simp only [List.length_map, List.length_take, List.getElem?_drop]
          congr 1; omega
      rw [← Hset]; iexact Hs
    ipureintro; exact ⟨by word, by word⟩
  · have HkN : sint.nat n = es.length := by word
    rw [HkN, List.take_length, List.drop_length, List.append_nil] at *
    iapply HΦ
    iexact Hs

end proof

end smd
end EtcdGrove
end Perennial
