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

/-- `minRV`'s strings all parse. -/
private theorem minRVL_parse (m d : w64) (c : Obj) (hasC : Bool) :
    (parseRVD (minRVL m d c hasC)).isSome := by
  unfold minRVL
  repeat' split
  all_goals simp [parseRVD, rvBytes]

set_option hygiene false in
/-- The final check of an input: `GenIn` and its cached object. -/
local macro "gen_fin" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> (try cases hasC) <;>
    first | exact hvb | simp [GenIn, CachedNoRV, withPreL, parseRVD, hgk]))

set_option hygiene false in
/-- `if rj == 0 { in.Reject = vals[ri] }; return in`, at index `I` of `vals`. -/
local macro "reject_tail " I:term:max : tactic => `(tactic| (
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr3)]
    list_elem wvsD (sint.Z $I).toNat as r
    wp_apply wp_load_slice_index _ (sint.Z $I) wvsD _ r hr3.1 $$ [Hv] as Hv
    · iframe; ipureintro; exact Hr_lookup
    (try wp_auto)
    iapply HΦ; ipureintro; gen_fin
  · (try wp_auto)
    iapply HΦ; ipureintro; gen_fin))

set_option maxHeartbeats 1600000 in
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
  wp_apply wp_pick n (W64 75) (by decide)
  (try wp_auto)
  rw [hkl]
  wp_apply wp_pick (n / W64 75) (W64 3) (by decide)
  (try wp_auto)
  -- `keys[ki]`
  have hk3 : 0 ≤ sint.Z (n / W64 75 % W64 3) ∧ sint.Z (n / W64 75 % W64 3) < sint.Z ksl.len := by
    rw [hkl]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hk3)]
  list_elem wksD (sint.Z (n / W64 75 % W64 3)).toNat as k
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 75 % W64 3)) wksD _ k hk3.1 $$ [Hk] as Hk
  · iframe; ipureintro; exact Hk_lookup
  have hkm : k ∈ wksD := List.mem_of_getElem? Hk_lookup
  have hgk : k = go!"a" ∨ k = go!"b" ∨ k = go!"c" := by simpa [wksD] using hkm
  (try wp_auto)
  wp_if_destruct
  · -- create
    rw [hvl]
    wp_apply wp_pick (n / W64 75 / W64 3) (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_pick (n / W64 75 / W64 3 / W64 3) (W64 65536) (by decide)
    (try wp_auto)
    have hv3 : 0 ≤ sint.Z (n / W64 75 / W64 3 % W64 3) ∧
        sint.Z (n / W64 75 / W64 3 % W64 3) < sint.Z vsl.len := by
      rw [hvl]; constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv3)]
    list_elem wvsD (sint.Z (n / W64 75 / W64 3 % W64 3)).toNat as v
    wp_apply wp_load_slice_index _ (sint.Z (n / W64 75 / W64 3 % W64 3)) wvsD _ v hv3.1 $$ [Hv]
      as Hv
    · iframe; ipureintro; exact Hv_lookup
    have hvb : v.length ≤ 2 ^ 20 := by
      have h := List.mem_of_getElem? Hv_lookup
      simp only [wvsD, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide
    (try wp_auto)
    wp_apply wp_uidOf
    (try wp_auto)
    iapply HΦ
    ipureintro
    refine ⟨⟨hgk, by simp, hvb, by simp [uidOfL], by simp [parseRVD], by simp [CachedNoRV]⟩,
      by simp⟩
  wp_if_destruct
  · -- delete
    wp_apply wp_pick _ (W64 4) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 4) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 4) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 4) (by decide)
    (try wp_auto)
    rw [hvl]
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_withPre
    (try wp_auto)
    have hr3 : 0 ≤ sint.Z (n / W64 75 / W64 3 / W64 4 / W64 4 / W64 4 / W64 4 % W64 3) ∧
        sint.Z (n / W64 75 / W64 3 / W64 4 / W64 4 / W64 4 / W64 4 % W64 3) < sint.Z vsl.len := by
      rw [hvl]; constructor <;> word
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        reject_tail (n / W64 75 / W64 3 / W64 4 / W64 4 / W64 4 / W64 4 % W64 3)
      · (try wp_auto)
        reject_tail (n / W64 75 / W64 3 / W64 4 / W64 4 / W64 4 / W64 4 % W64 3)
    · (try wp_auto)
      reject_tail (n / W64 75 / W64 3 / W64 4 / W64 4 / W64 4 / W64 4 % W64 3)
  wp_if_destruct
  · -- get
    wp_apply wp_pick _ (W64 2) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 100) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 200) (by decide)
    (try wp_auto)
    wp_apply wp_minRV
    (try wp_auto)
    have hm := minRVL_parse (n / W64 75 / W64 3 / W64 2 % W64 100)
      (n / W64 75 / W64 3 / W64 2 / W64 100 % W64 200 + W64 1) c hasC
    iapply HΦ; ipureintro
    refine ⟨⟨?_, ?_, ?_, ?_, hm, ?_⟩, ?_⟩ <;> simp [GenIn, CachedNoRV, hgk]
  -- update
  rw [hvl]
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 5) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 5) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 4) (by decide)
  (try wp_auto)
  rw [hvl]
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  have hv3 : 0 ≤ sint.Z (n / W64 75 / W64 3 % W64 3) ∧
      sint.Z (n / W64 75 / W64 3 % W64 3) < sint.Z vsl.len := by
    rw [hvl]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hv3)]
  list_elem wvsD (sint.Z (n / W64 75 / W64 3 % W64 3)).toNat as v
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 75 / W64 3 % W64 3)) wvsD _ v hv3.1 $$ [Hv]
    as Hv
  · iframe; ipureintro; exact Hv_lookup
  have hvb : v.length ≤ 2 ^ 20 := by
    have h := List.mem_of_getElem? Hv_lookup
    simp only [wvsD, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  (try wp_auto)
  have hr3 : 0 ≤ sint.Z (n / W64 75 / W64 3 / W64 3 / W64 5 / W64 5 / W64 100 / W64 100 / W64 100 /
        W64 4 % W64 3) ∧
      sint.Z (n / W64 75 / W64 3 / W64 3 / W64 5 / W64 5 / W64 100 / W64 100 / W64 100 / W64 4 %
        W64 3) < sint.Z vsl.len := by
    rw [hvl]; constructor <;> word
  repeat' (first | wp_if_destruct | wp_apply wp_withPre | wp_auto)
  all_goals first
    | (rw [ite_eq_left_of_eq_true _ _ (eq_true hr3)]
       list_elem wvsD (sint.Z (n / W64 75 / W64 3 / W64 3 / W64 5 / W64 5 / W64 100 / W64 100 /
         W64 100 / W64 4 % W64 3)).toNat as r
       wp_apply wp_load_slice_index _ _ wvsD _ r hr3.1 $$ [Hv] as Hv
       · iframe; ipureintro; exact Hr_lookup
       (try wp_auto)
       iapply HΦ; ipureintro; gen_fin)
    | (iapply HΦ; ipureintro; gen_fin)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
