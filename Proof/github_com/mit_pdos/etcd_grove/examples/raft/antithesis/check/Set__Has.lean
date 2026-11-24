/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Set.Has`.
-/
module

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

theorem Set.Has.wp_proof : Set.Has.spec (GF := GF) (hG := hG) := by
  intro sl xs x
  wp_start as #Hxs
  iunfold strsRO at Hxs
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  ihave IH : iprop(∃ (n : w64) (y : Str),
      "i" ∷ i_ptr ↦ n ∗ "y" ∷ y_ptr ↦ y ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ x ∉ xs.take (sint.nat n)⌝) $$ [i y]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨z, Hz⟩ : ∃ z, xs[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard z Hn.1 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hz
    try wp_auto
    wp_if_destruct
    · wp_for_post
      try wp_auto
      have : SSet.has xs x = true := by
        unfold SSet.has; rw [List.contains_iff_mem, ← Hif]; exact List.mem_of_getElem? Hz
      rw [this]
      iapply HΦ; ipureintro; trivial
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [h1, List.take_add_one, Hz]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hn.2.2, fun h => Hif (h ▸ rfl)⟩
  · try wp_auto
    have : SSet.has xs x = false := by
      unfold SSet.has
      rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
      have : sint.nat n = xs.length := by rw [Hlen.1]; word
      have h := Hn.2.2; rw [this, List.take_length] at h; exact h
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
