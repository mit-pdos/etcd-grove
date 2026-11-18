/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Set__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Equal

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

theorem Set.Equal.wp_proof : Set.Equal.spec (GF := GF) (hG := hG) := by
  intro sl s tl t
  wp_start as ⟨#Hs, #Ht⟩
  iunfold setRO at Hs Ht
  icases Hs with ⟨%xs, #Hxs, %Hxm⟩
  icases Ht with ⟨%ys, #Hys, %Hym⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  ihave %Hyl := ownSlice_len $$ Hys
  wp_auto
  wp_if_destruct
  · have hxy : xs.length = ys.length := by rw [Hxl.1, Hyl.1, Hif]
    ihave IH : iprop(∃ (n kv : w64),
        "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ xs.take (sint.nat n) = ys.take (sint.nat n)⌝)
        $$ [i k]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IH
    obtain ⟨hn0, hn1, hnt⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < xs.length := by rw [Hxl.1]; word
      obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨y, Hy⟩ : ∃ y, ys[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem (hxy ▸ Hlt)⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hx
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hx
      try wp_auto
      have Hif' : sint.Z n < sint.Z tl.len := by
        have : sint.nat n < ys.length := hxy ▸ Hlt
        rw [Hyl.1] at this; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z tl.len from ⟨hn0, Hif'⟩))]
      wp_apply wp_load_slice_index tl (sint.Z n) ys DFrac.discard y hn0 $$ [Hys] as -
      · isplitr
        · iexact Hys
        ipureintro; exact Hy
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, List.take_add_one,
          hnt, Hx, Hy, Hif]
      · -- `s[k] != t[k]`
        try wp_auto
        wp_for_post
        try wp_auto
        have : decide (s = t) = false := by
          rw [decide_eq_false_iff_not]; intro h
          have h2 := Hxm.trans (h.trans Hym.symm)
          have h3 := congrArg (fun l => l[sint.nat n]?) h2
          simp only [List.getElem?_map, Hx, Hy, Option.map_some, Option.some.injEq] at h3
          exact Hif (word.unsigned_inj (by have := congrArg (fun n : Nat => (n : Int)) h3; simpa using this))
        rw [this]
        iapply HΦ; ipureintro; trivial
    · try wp_auto
      have hnx : sint.nat n = xs.length := by rw [Hxl.1]; word
      have : decide (s = t) = true := by
        rw [decide_eq_true_iff, ← Hxm, ← Hym]
        rw [hnx, List.take_length, hxy, List.take_length] at hnt
        rw [hnt]
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : decide (s = t) = false := by
      rw [decide_eq_false_iff_not]; intro h
      apply Hif
      have := congrArg List.length (Hxm.trans (h.trans Hym.symm))
      simp only [List.length_map] at this
      rw [Hxl.1, Hyl.1] at this; word
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
