/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `interCount`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.interCount
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Has

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem interCount.wp_proof (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    interCount.spec (GF := GF) (hG := hG) := by
  intro sl xs tl ys
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hxs := Hs
  iunfold strsRO at Hxs
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  ihave IH : iprop(∃ (n c : w64) (y : Str),
      "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ y ∗ "n" ∷ n_ptr ↦ c ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        sint.Z c = interCount (xs.take (sint.nat n)) ys⌝) $$ [i x n]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp [interCount]⟩
  wp_for IH
  obtain ⟨hn0, hn1, hc⟩ := Hn
  have hcle : interCount (xs.take (sint.nat n)) ys ≤ sint.nat n := by
    unfold interCount
    exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨z, Hz⟩ : ∃ z, xs[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard z hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hz
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set.TypeAssumptions.ptr_Has_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Has tl ys z $$ [Ht]
    · iexact Ht
    have htake : interCount (xs.take (sint.nat (n + W64 1))) ys =
        interCount (xs.take (sint.nat n)) ys + (if SSet.has ys z then 1 else 0) := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hz]
      unfold interCount
      by_cases hh : SSet.has ys z <;> simp [List.filter_append, hh]
    cases hh : SSet.has ys z
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, hh]; simpa using hc
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, hh]
      simp only [ite_true]
      push_cast
      rw [← hc]
      have : sint.Z c ≤ sint.Z n := by
        have := hcle; have : (sint.nat n : Int) = sint.Z n := by word
        omega
      word
  · try wp_auto
    have hnx : sint.nat n = xs.length := by rw [Hlen.1]; word
    rw [hnx, List.take_length] at hc
    iapply HΦ; ipureintro; exact hc

end proof

end AntCheck
end EtcdGrove
end Perennial
