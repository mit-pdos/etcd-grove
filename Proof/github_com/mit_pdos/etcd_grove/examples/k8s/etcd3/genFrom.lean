module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.uidOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.withPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.minRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadKeys
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadVals
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadNodes
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadApps
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genList
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- `L[I]` of the slice `sl ↦* L` (`Hs`), whose length is `hl`, as `v` (with `hm : v ∈ L`). -/
local macro "load_elem " L:term:max sl:ident hl:ident I:term:max Hs:ident " as " v:ident hm:ident :
    tactic => `(tactic| (
  have hb : 0 ≤ sint.Z $I ∧ sint.Z $I < sint.Z ($sl).len := by rw [$hl:ident]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  list_elem $L (sint.Z $I).toNat as $v
  wp_apply wp_load_slice_index _ (sint.Z $I) $L _ $v hb.1 $$ [$Hs:ident] as $Hs:ident
  · iframe; ipureintro; assumption
  have $hm : $v ∈ $L := List.mem_of_getElem? (by assumption)
  clear hb))

theorem wvsD_len (v : GoString) (h : v ∈ wvsD) : v.length ≤ 2 ^ 20 := by
  simp only [wvsD, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

theorem wndD_len (v : GoString) (h : v ∈ wndD) : v.length < 256 := by
  simp only [wndD, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

theorem wapD_len (v : GoString) (h : v ∈ wapD) : v.length < 256 := by
  simp only [wapD, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem genFrom.wp_proof (wp_workloadKeys : workloadKeys.spec (GF := GF) (hG := hG))
    (wp_workloadVals : workloadVals.spec (GF := GF) (hG := hG))
    (wp_workloadNodes : workloadNodes.spec (GF := GF) (hG := hG))
    (wp_workloadApps : workloadApps.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_uidOf : uidOf.spec (GF := GF) (hG := hG))
    (wp_withPre : withPre.spec (GF := GF) (hG := hG))
    (wp_minRV : minRV.spec (GF := GF) (hG := hG))
    (wp_genList : genList.spec (GF := GF) (hG := hG)) :
    genFrom.spec (GF := GF) (hG := hG) := by
  intro n id c hasC
  wp_start
  wp_auto
  wp_apply wp_workloadKeys as %ksl ⟨Hk, -⟩
  (try wp_auto)
  wp_apply wp_workloadVals as %vsl ⟨Hv, -⟩
  (try wp_auto)
  wp_apply wp_workloadNodes as %nsl ⟨Hn, -⟩
  (try wp_auto)
  wp_apply wp_workloadApps as %asl ⟨Ha, -⟩
  (try wp_auto)
  ihave %Hkl := ownSlice_len $$ Hk
  ihave %Hvl := ownSlice_len $$ Hv
  ihave %Hnl := ownSlice_len $$ Hn
  ihave %Hal := ownSlice_len $$ Ha
  have hkl : ksl.len = W64 4 := by
    have := Hkl.1; simp only [List.length_cons, List.length_nil] at this; word
  have hvl : vsl.len = W64 3 := by
    have := Hvl.1; simp only [List.length_cons, List.length_nil] at this; word
  have hnl : nsl.len = W64 3 := by
    have := Hnl.1; simp only [List.length_cons, List.length_nil] at this; word
  have hal : asl.len = W64 3 := by
    have := Hal.1; simp only [List.length_cons, List.length_nil] at this; word
  clear Hkl Hvl Hnl Hal
  wp_apply wp_pick n (W64 100) (by decide)
  (try wp_auto)
  rw [hkl]
  wp_apply wp_pick (n / W64 100) (W64 4) (by decide)
  (try wp_auto)
  load_elem wksD ksl hkl (n / W64 100 % W64 4) Hk as k hgk
  (try wp_auto)
  wp_if_destruct
  · -- create
    rw [hvl]
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    rw [hnl]
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    rw [hal]
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_pick _ (W64 65536) (by decide)
    (try wp_auto)
    load_elem wvsD vsl hvl (n / W64 100 / W64 4 % W64 3) Hv as v hv
    (try wp_auto)
    load_elem wndD nsl hnl (n / W64 100 / W64 4 / W64 3 % W64 3) Hn as nd hnd
    (try wp_auto)
    load_elem wapD asl hal (n / W64 100 / W64 4 / W64 3 / W64 3 % W64 3) Ha as ap hap
    (try wp_auto)
    wp_apply wp_uidOf
    (try wp_auto)
    iapply HΦ; ipureintro
    refine ⟨⟨⟨hgk, by simp [uidOfL], wndD_len _ hnd, wapD_len _ hap, ⟨0, rfl, by decide⟩,
      by intro h; simp only [] at h; exact absurd h (by decide)⟩, by simp, wvsD_len _ hv, by simp [CachedNoRV]⟩, by simp⟩
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
    rw [hnl]
    wp_apply wp_pick _ (W64 3) (by decide)
    (try wp_auto)
    wp_apply wp_withPre
    (try wp_auto)
    repeat' wp_if_destruct
    all_goals (try (load_elem wndD nsl hnl (n / W64 100 / W64 4 / W64 4 / W64 4 / W64 4 / W64 4 % W64 3) Hn as r hr))
    all_goals ((try wp_auto); iapply HΦ; ipureintro)
    all_goals (try cases hasC) <;> (
      simp only [withPreL, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨⟨hgk, by simp, by simp, by simp, ⟨0, rfl, by decide⟩,
        by intro h; simp only [] at h; exact absurd h (by decide)⟩, by simp, by simp,
        by simp [CachedNoRV]⟩, by simp⟩)
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
    obtain ⟨k', hk1, hk2⟩ := minRVL_ok (n / W64 100 / W64 4 / W64 2 % W64 100)
      (n / W64 100 / W64 4 / W64 2 / W64 100 % W64 200 + W64 1) c hasC (by word)
    iapply HΦ; ipureintro
    refine ⟨⟨⟨hgk, by simp, by simp, by simp, ⟨k', hk1, hk2⟩,
      by intro h; simp only [] at h; exact absurd h (by decide)⟩, by simp, by simp,
      by simp [CachedNoRV]⟩, by simp⟩
  wp_if_destruct
  · -- list
    wp_apply wp_genList as %y %Hy
    all_goals first
      | (ipureintro; first | exact hgk | (simp only []; decide))
      | (iapply HΦ; ipureintro
         exact ⟨Hy.1, fun h => by rw [Hy.2] at h; simp at h⟩)
  -- update
  rw [hvl]
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  rw [hnl]
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  rw [hal]
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
  rw [hnl]
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  load_elem wvsD vsl hvl (n / W64 100 / W64 4 % W64 3) Hv as v hv
  (try wp_auto)
  load_elem wndD nsl hnl (n / W64 100 / W64 4 / W64 3 % W64 3) Hn as nd hnd
  (try wp_auto)
  load_elem wapD asl hal (n / W64 100 / W64 4 / W64 3 / W64 3 % W64 3) Ha as ap hap
  (try wp_auto)
  repeat' (first | wp_if_destruct | (wp_apply wp_withPre; (try wp_auto)))
  all_goals (try (load_elem wndD nsl hnl (n / W64 100 / W64 4 / W64 3 / W64 3 / W64 3 / W64 5 / W64 5 / W64 100 / W64 100 / W64 100 / W64 4 % W64 3) Hn as r hr))
  all_goals ((try wp_auto); iapply HΦ; ipureintro)
  all_goals (try cases hasC) <;> (
    simp only [withPreL, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨⟨hgk, by simp, wndD_len _ hnd, wapD_len _ hap, ⟨0, rfl, by decide⟩,
      by intro h; simp only [] at h; exact absurd h (by decide)⟩, by simp, wvsD_len _ hv,
      by simp [CachedNoRV]⟩, by simp⟩)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
