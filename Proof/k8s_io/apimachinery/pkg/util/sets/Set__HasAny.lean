/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/Set__HasAny.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__HasAny
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem Set.HasAny.wp_proof (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    Set.HasAny.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ _ m dq s sl dl ks
  wp_start as ⟨Hm, Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : K),
      "i" ∷ i_ptr ↦ n ∗
      "item" ∷ item_ptr ↦ x ∗
      "%Hnone" ∷ ⌜∀ k ∈ ks.take (sint.nat n), (s !! k).isSome = false⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ks.length⌝) $$ [i item]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨by intro k hk; rw [show sint.nat (W64 0) = 0 by rfl] at hk; simp at hk, by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ks.length := by word
    obtain ⟨e, He⟩ : ∃ e, ks[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ks dl e Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact He
    wp_apply (Set.wp_ptr_Has_of wp_Has) $$ [$s $Hm] as ⟨s, Hm⟩
    have hmem : e ∈ ks := List.mem_of_getElem? He
    cases hk : (s !! e).isSome with
    | true =>
      simp only [_root_.decide_true]
      wp_auto
      wp_for_post
      have : decide (∃ k ∈ ks, (s !! k).isSome) = true := by
        simp only [decide_eq_true_eq]; exact ⟨e, hmem, hk⟩
      rw [this]
      iapply HΦ
      iframe
    | false =>
      simp only [Bool.false_eq_true, _root_.decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, e
      iframe
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
        have := Hn.1; have := Hlt; have := Hlen.1; word
      have Htake : ks.take (sint.nat (n + W64 1)) = ks.take (sint.nat n) ++ [e] := by
        rw [hn1, List.take_add_one, He]; rfl
      have h1 : 0 ≤ sint.Z (n + W64 1) := by have := Hn.1; have := Hlt; have := Hlen.1; word
      have h2 : sint.nat (n + W64 1) ≤ ks.length := by rw [hn1]; omega
      ipureintro
      refine ⟨?_, h1, h2⟩
      rw [Htake]
      intro k hk'
      rcases List.mem_append.mp hk' with h | h
      · exact Hnone k h
      · rw [List.mem_singleton] at h; subst h; exact hk
  · rw [show sint.nat n = ks.length by word, List.take_length] at Hnone
    have : decide (∃ k ∈ ks, (s !! k).isSome) = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro k hk hs
      rw [Hnone k hk] at hs; cases hs
    rw [this]
    iapply HΦ
    iframe

end proof

end sets
end EtcdGrove
end Perennial
