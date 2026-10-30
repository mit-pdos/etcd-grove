module
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElements
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

theorem Page.LeafPageElements.wp_proof (hUnsafeAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    Page.LeafPageElements.spec (GF := GF) (hG := hG) := by
  intro l v dq Hc
  wp_start as Hl
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true Hif)]
    iapply HΦ; iframe
  wp_apply hUnsafeAdd
  try wp_auto
  wp_func_call
  try wp_auto
  rw [decide_eq_false (by word)]
  try wp_auto
  rw [decide_eq_false (loc_add_ne_null l _ Hc), typeSize_leafPageElement (hG := hG)]
  try wp_auto
  rw [decide_eq_false (by word)]
  try wp_auto
  rw [ite_eq_right_of_eq_false _ _ (eq_false Hif), show sint.Z (W64 16) = 16 by rfl]
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
