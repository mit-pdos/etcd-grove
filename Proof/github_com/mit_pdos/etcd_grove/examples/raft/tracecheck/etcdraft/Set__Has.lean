/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08): the proof of `Set__Has`.
-/
module

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

theorem Set.Has.wp_proof : Set.Has.spec (GF := GF) (hG := hG) := by
  intro sl s id
  wp_start as #Hs
  iunfold setRO at Hs
  icases Hs with ⟨%xs, #Hxs, %Hmap⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  have Hin : ∀ y : w64, (uint.nat y ∈ s ↔ y ∈ xs) := by
    intro y; rw [← Hmap, List.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := by apply word.unsigned_inj; have := congrArg (fun n : Nat => (n : Int)) hzy; simpa using this
      rw [← this]; exact hz
    · intro hy; exact ⟨y, hy, rfl⟩
  ihave IH : iprop(∃ (n x : w64),
      "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ id ∉ xs.take (sint.nat n)⌝) $$ [i x]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard y Hn.1 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    wp_if_destruct
    · -- found
      wp_for_post
      try wp_auto
      have : decide (uint.nat id ∈ s) = true := by
        rw [decide_eq_true_iff, Hin]; rw [← Hif]; exact List.mem_of_getElem? Hy
      rw [this]
      iapply HΦ; ipureintro; trivial
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [h1, List.take_add_one, Hy]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hn.2.2, fun h => Hif (h ▸ rfl)⟩
  · try wp_auto
    have : decide (uint.nat id ∈ s) = false := by
      rw [decide_eq_false_iff_not, Hin]
      have : sint.nat n = xs.length := by rw [Hlen.1]; word
      have h := Hn.2.2; rw [this, List.take_length] at h; exact h
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
