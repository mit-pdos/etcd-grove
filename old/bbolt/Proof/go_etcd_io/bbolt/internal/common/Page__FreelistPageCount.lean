module
public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageCount
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Page.FreelistPageCount.wp_proof (hF : Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (hUnsafeAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    Page.FreelistPageCount.spec (GF := GF) (hG := hG) := by
  intro l v dq c Hfl Hc
  wp_start as ⟨Hl, Hcell⟩
  wp_auto
  wp_apply hF $$ [$Hl] as Hl
  rw [decide_eq_true Hfl]
  try wp_auto
  by_cases Ho : fpOverflow v
  · have Hv : v.count' = W16 65535 := Ho
    rw [decide_eq_true (show W64 (uint.Z v.count') = W64 65535 by rw [Hv]; rfl)]
    try wp_auto
    wp_apply hUnsafeAdd
    unfold fpCountCell
    rw [ite_eq_left_of_eq_true _ _ (eq_true Ho)]
    rw [show sint.Z (W64 16) = 16 by rfl]
    try wp_auto
    rw [decide_eq_false (by have := Hc Ho; word)]
    try wp_auto
    unfold fpIdx fpCount
    rw [ite_eq_left_of_eq_true _ _ (eq_true Ho), ite_eq_left_of_eq_true _ _ (eq_true Ho)]
    iapply HΦ; iframe
  · have Hv : ¬ v.count' = W16 65535 := Ho
    rw [decide_eq_false (show ¬ W64 (uint.Z v.count') = W64 65535 by
      intro h; apply Hv; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h
      simp at this ⊢; omega)]
    try wp_auto
    unfold fpIdx fpCount
    rw [ite_eq_right_of_eq_false _ _ (eq_false Ho), ite_eq_right_of_eq_false _ _ (eq_false Ho)]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
