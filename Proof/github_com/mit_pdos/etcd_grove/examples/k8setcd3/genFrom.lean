module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.genFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.workloadKeys
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.workloadVals
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.pick

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem genFrom.wp_proof (wp_workloadKeys : workloadKeys.spec (GF := GF) (hG := hG))
    (wp_workloadVals : workloadVals.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG)) :
    genFrom.spec (GF := GF) (hG := hG) := by
  intro n
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
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inl rfl⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inl rfl)⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inl rfl))⟩
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inr rfl))⟩
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inl rfl⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inl rfl)⟩
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inl rfl))⟩
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨hgk, Or.inr (Or.inr (Or.inr rfl))⟩

end proof

end k8setcd3
end EtcdGrove
end Perennial
