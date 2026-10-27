/-
Lean-first (no Rocq counterpart).

The proof of `genFrom`: the picks, the key and the value (in bounds, modulo the slices'
lengths), then one input per weight, each one `Apply` takes (`GenLemmas.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.genFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.workloadKeys
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.pick

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem genFrom.wp_proof (wp_workloadKeys : workloadKeys.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG)) :
    genFrom.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_apply wp_workloadKeys as %ksl ⟨Hk, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal (l := [go!"a", go!"b", go!"c", go!"d"])
  isplitr
  · ipureintro; rfl
  iintro %vsl ⟨Hv, -⟩
  ihave %Hkl := ownSlice_len $$ Hk
  ihave %Hvl := ownSlice_len $$ Hv
  (try wp_auto)
  wp_apply wp_pick n (W64 63) (by decide)
  (try wp_auto)
  have hkl : ksl.len = W64 3 := by
    have := Hkl.1; simp only [List.length_cons, List.length_nil] at this; word
  rw [hkl]
  wp_apply wp_pick (n / W64 63) (W64 3) (by decide)
  (try wp_auto)
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (4 : Int) 0) 0 = 4 from rfl] at Hvl ⊢
  wp_apply wp_pick (n / W64 63 / W64 3) (W64 4) (by decide)
  (try wp_auto)
  -- `keys[ki]`, `vals[vi]`
  have hk3 : 0 ≤ sint.Z (n / W64 63 % W64 3) ∧ sint.Z (n / W64 63 % W64 3) < sint.Z ksl.len := by
    rw [hkl]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hk3)]
  list_elem wks (sint.Z (n / W64 63 % W64 3)).toNat as k
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 63 % W64 3)) wks _ k hk3.1 $$ [Hk] as Hk
  · iframe; ipureintro; exact Hk_lookup
  have hkm : k ∈ wks := List.mem_of_getElem? Hk_lookup
  (try wp_auto)
  have hv4 : 0 ≤ sint.Z (n / W64 63 / W64 3 % W64 4) ∧
      sint.Z (n / W64 63 / W64 3 % W64 4) < sint.Z (W64 4) := by constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hv4)]
  list_elem [go!"a", go!"b", go!"c", go!"d"] (sint.Z (n / W64 63 / W64 3 % W64 4)).toNat as v
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 63 / W64 3 % W64 4)) _ _ v hv4.1 $$ [Hv] as Hv
  · iframe; ipureintro; exact Hv_lookup
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; ipureintro; exact genIn_key _ (fun _ => hkm) (Or.inl rfl)
  wp_if_destruct
  · iapply HΦ; ipureintro; exact genIn_key _ (fun h => absurd rfl h) (Or.inr (Or.inl rfl))
  wp_if_destruct
  · iapply HΦ; ipureintro; exact genIn_key _ (fun _ => hkm) (Or.inr (Or.inr (Or.inl rfl)))
  wp_if_destruct
  · iapply HΦ; ipureintro; exact genIn_key _ (fun _ => hkm) (Or.inr (Or.inr (Or.inr rfl)))
  wp_if_destruct
  · -- a transaction of one to three operations
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk3)]
    wp_apply wp_load_slice_index _ (sint.Z (n / W64 63 % W64 3)) wks _ k hk3.1 $$ [Hk] as Hk
    · iframe; ipureintro; exact Hk_lookup
    (try wp_auto)
    rw [hkl]
    simp only [show ¬ uint.Z (W64 3) = 0 from by decide, ↓reduceIte]
    (try wp_auto)
    have hi1 : 0 ≤ sint.Z ((n / W64 63 % W64 3 + W64 1) % W64 3) ∧
        sint.Z ((n / W64 63 % W64 3 + W64 1) % W64 3) < sint.Z ksl.len := by
      rw [hkl]; constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi1)]
    list_elem wks (sint.Z ((n / W64 63 % W64 3 + W64 1) % W64 3)).toNat as k1
    wp_apply wp_load_slice_index _ _ wks _ k1 hi1.1 $$ [Hk] as Hk
    · iframe; ipureintro; exact Hk1_lookup
    (try wp_auto)
    rw [hkl]
    simp only [show ¬ uint.Z (W64 3) = 0 from by decide, ↓reduceIte]
    (try wp_auto)
    have hi2 : 0 ≤ sint.Z ((n / W64 63 % W64 3 + W64 2) % W64 3) ∧
        sint.Z ((n / W64 63 % W64 3 + W64 2) % W64 3) < sint.Z ksl.len := by
      rw [hkl]; constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi2)]
    list_elem wks (sint.Z ((n / W64 63 % W64 3 + W64 2) % W64 3)).toNat as k2
    wp_apply wp_load_slice_index _ _ wks _ k2 hi2.1 $$ [Hk] as Hk
    · iframe; ipureintro; exact Hk2_lookup
    (try wp_auto)
    iapply HΦ
    ipureintro
    have hk1m : k1 ∈ wks := List.mem_of_getElem? Hk1_lookup
    have hk2m : k2 ∈ wks := List.mem_of_getElem? Hk2_lookup
    refine genIn_txn' _ rfl (by word) (by word) (by word) (by word) (by word) (by word) ?_ ?_ ?_
    · intro c hc
      simp [cmpsOfL] at hc
    · intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · rcases thenOfL_subset _ o ho with rfl | rfl | rfl
        · exact ⟨by word, hkm⟩
        · exact ⟨by word, hk1m⟩
        · exact ⟨by word, hk2m⟩
      · simp [elseOfL] at ho
    · intro h
      have h0 : 0 < sint.Z (n / W64 63 / W64 3 / W64 4 % W64 3 + W64 1) := by word
      unfold thenOfL at h
      simp only [h0, ↓reduceIte] at h
      simp at h
  -- a compare-and-set
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 4) (by decide)
  (try wp_auto)
  have hn4 : 0 ≤ sint.Z ((n / W64 63 / W64 3 % W64 4 + W64 1) % W64 4) ∧
      sint.Z ((n / W64 63 / W64 3 % W64 4 + W64 1) % W64 4) < sint.Z (W64 4) := by
    constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hn4)]
  list_elem [go!"a", go!"b", go!"c", go!"d"] (sint.Z ((n / W64 63 / W64 3 % W64 4 + W64 1) %
    W64 4)).toNat as nv
  wp_apply wp_load_slice_index _ _ _ _ nv hn4.1 $$ [Hv] as Hv
  · iframe; ipureintro; exact Hnv_lookup
  (try wp_auto)
  iapply HΦ
  ipureintro
  have h1 : sint.Z (W64 1) = 1 := by word
  refine genIn_txn' _ rfl (by word) (by word) (by word) (by word) (by word) (by word) ?_ ?_ ?_
  · intro c hc
    simp only [cmpsOfL, h1, Int.zero_lt_one, ↓reduceIte, List.mem_singleton] at hc
    subst hc
    word
  · intro o ho
    simp only [thenOfL, elseOfL, h1, Int.zero_lt_one, ↓reduceIte, List.mem_append,
      List.mem_singleton] at ho
    simp only [show ¬ (1 : Int) < 1 from by omega, show ¬ (2 : Int) < 1 from by omega,
      ↓reduceIte] at ho
    simp only [List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨by simp only; word, hkm⟩
    · exact ⟨by simp only; word, hkm⟩
  · simp [thenOfL]

end proof

end linkvtxn
end EtcdGrove
end Perennial
