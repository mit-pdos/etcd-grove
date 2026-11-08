/-
Lean-first (no Rocq counterpart). Layer C (2026-11-08): the proof of `Set__Subset`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Subset
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Has

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Set.Subset.wp_proof (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    Set.Subset.spec (GF := GF) (hG := hG) := by
  intro sl s tl t
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hs0 := Hs
  iunfold setRO at Hs0
  icases Hs0 with ⟨%xs, #Hxs, %Hmap⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  ihave IH : iprop(∃ (n x : w64),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        ∀ y ∈ xs.take (sint.nat n), uint.nat y ∈ t⌝) $$ [i id]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by clear hnt; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Has_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Has tl t y $$ [Ht]
    · iexact Ht
    by_cases hy : uint.nat y ∈ t
    · simp only [hy, decide_true, Bool.not_true]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hnt; word, by clear hnt; word, ?_⟩
      have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hnt; word
      rw [h1, List.take_add_one, Hy]
      intro z hz
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | hz
      · exact hnt z hz
      · subst hz; exact hy
    · simp only [hy, decide_false, Bool.not_false]
      try wp_auto
      wp_for_post
      try wp_auto
      have : s.subset t = false := by
        unfold SetIds.subset
        rw [List.all_eq_false]
        refine ⟨uint.nat y, ?_, ?_⟩
        · rw [← Hmap]; exact List.mem_map_of_mem (List.mem_of_getElem? Hy)
        · simpa [List.contains_iff_mem] using hy
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : s.subset t = true := by
      unfold SetIds.subset
      rw [List.all_eq_true]
      intro z hz
      rw [← Hmap] at hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      have : sint.nat n = xs.length := by clear hnt; rw [Hlen.1]; word
      have h := hnt; rw [this, List.take_length] at h
      simpa [List.contains_iff_mem] using h y hy
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
