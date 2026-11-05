module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.uidOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.withPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.minRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadKeys
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadVals
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pick

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem genFrom.wp_proof (wp_workloadKeys : workloadKeys.spec (GF := GF) (hG := hG))
    (wp_workloadVals : workloadVals.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_uidOf : uidOf.spec (GF := GF) (hG := hG))
    (wp_withPre : withPre.spec (GF := GF) (hG := hG))
    (wp_minRV : minRV.spec (GF := GF) (hG := hG)) :
    genFrom.spec (GF := GF) (hG := hG) := by
  intro n id c hasC
  wp_start
  wp_auto
  wp_apply wp_workloadKeys as %ksl ⟨Hk, -⟩
  (try wp_auto)
  wp_apply wp_workloadVals as %vsl ⟨Hv, -⟩
  (try wp_auto)
  ihave %Hkl := ownSlice_len $$ Hk
  ihave %Hvl := ownSlice_len $$ Hv
  have hkl : ksl.len = W64 3 := by
    have := Hkl.1; simp only [List.length_cons, List.length_nil] at this; word
  have hvl : vsl.len = W64 3 := by
    have := Hvl.1; simp only [List.length_cons, List.length_nil] at this; word
  -- Stage 7b: genFrom draws with the weights out of 75 and the new fields (UID, preconditions, cached object, ignoreNotFound, minimum resource version); the proof below is 6f's (commit 835795d4d1 (lean)), for the Prove phase
  sorry
/- the rest of the proof at 835795d4d1 (lean):
  wp_apply wp_pick n (W64 100) (by decide)
  (try wp_auto)
  rw [hkl]
  wp_apply wp_pick (n / W64 100) (W64 3) (by decide)
  (try wp_auto)
  rw [hvl]
  wp_apply wp_pick (n / W64 100 / W64 3) (W64 3) (by decide)
  (try wp_auto)
  wp_apply wp_pick (n / W64 100 / W64 3 / W64 3) (W64 4) (by decide)
  (try wp_auto)
  rw [hvl]
  wp_apply wp_pick (n / W64 100 / W64 3 / W64 3 / W64 4) (W64 3) (by decide)
  (try wp_auto)
  wp_apply wp_pick (n / W64 100 / W64 3 / W64 3 / W64 4 / W64 3) (W64 5) (by decide)
  (try wp_auto)
  wp_apply wp_pick (n / W64 100 / W64 3 / W64 3 / W64 4 / W64 3 / W64 5) (W64 2) (by decide)
  (try wp_auto)
  -- `keys[ki]`, `vals[vi]`
  have hk3 : 0 ≤ sint.Z (n / W64 100 % W64 3) ∧ sint.Z (n / W64 100 % W64 3) < sint.Z ksl.len := by
    rw [hkl]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hk3)]
  list_elem wksD (sint.Z (n / W64 100 % W64 3)).toNat as k
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 100 % W64 3)) wksD _ k hk3.1 $$ [Hk] as Hk
  · iframe; ipureintro; exact Hk_lookup
  have hkm : k ∈ wksD := List.mem_of_getElem? Hk_lookup
  have hgk : k = go!"a" ∨ k = go!"b" ∨ k = go!"c" := by simpa [wksD] using hkm
  (try wp_auto)
  have hv3 : 0 ≤ sint.Z (n / W64 100 / W64 3 % W64 3) ∧
      sint.Z (n / W64 100 / W64 3 % W64 3) < sint.Z vsl.len := by
    rw [hvl]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hv3)]
  list_elem wvsD (sint.Z (n / W64 100 / W64 3 % W64 3)).toNat as v
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 100 / W64 3 % W64 3)) wvsD _ v hv3.1 $$ [Hv]
    as Hv
  · iframe; ipureintro; exact Hv_lookup
  have hvb : v.length ≤ 2 ^ 20 := by
    have h := List.mem_of_getElem? Hv_lookup
    simp only [wvsD, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  (try wp_auto)
  -- the rejected value, if any: `vals[ri]`
  wp_if_destruct
  · have hr3 : 0 ≤ sint.Z (n / W64 100 / W64 3 / W64 3 / W64 4 % W64 3) ∧
        sint.Z (n / W64 100 / W64 3 / W64 3 / W64 4 % W64 3) < sint.Z vsl.len := by
      rw [hvl]; constructor <;> word
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hr3)]
    list_elem wvsD (sint.Z (n / W64 100 / W64 3 / W64 3 / W64 4 % W64 3)).toNat as r
    wp_apply wp_load_slice_index _ _ wvsD _ r hr3.1 $$ [Hv] as Hv
    · iframe; ipureintro; exact Hr_lookup
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inl rfl, by first | exact hvb | simp⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inl rfl), by first | exact hvb | simp⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inl rfl)), by first | exact hvb | simp⟩
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inr rfl)), by first | exact hvb | simp⟩
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inl rfl, by first | exact hvb | simp⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inl rfl), by first | exact hvb | simp⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inl rfl)), by first | exact hvb | simp⟩
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inr rfl)), by first | exact hvb | simp⟩
-/

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
