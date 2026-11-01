module
public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageIds
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeIndex
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

theorem Page.FreelistPageIds.wp_proof (hF : Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (hC : Page.FreelistPageCount.spec (GF := GF) (hG := hG))
    (hUnsafeIndex : UnsafeIndex.spec (GF := GF) (hG := hG)) :
    Page.FreelistPageIds.spec (GF := GF) (hG := hG) := by
  intro l v dq c Hcar Hfl Hc
  wp_start as ⟨Hl, Hcell⟩
  wp_auto
  wp_apply hF $$ [$Hl] as Hl
  rw [decide_eq_true Hfl]
  try wp_auto
  wp_apply hC l v dq c Hfl Hc $$ [$Hl $Hcell] as ⟨Hl, Hcell⟩
  try wp_auto
  have Hcnt : 0 ≤ sint.Z (fpCount v c) := by
    unfold fpCount; split
    · exact Hc ‹_›
    · word
  have Hidx : uint.Z (fpIdx v) ≤ 1 := by unfold fpIdx; split <;> decide
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true Hif)]
    iapply HΦ; iframe
  try wp_auto
  wp_apply hUnsafeIndex
  try wp_auto
  wp_func_call
  try wp_auto
  rw [decide_eq_false (by word)]
  try wp_auto
  rw [decide_eq_false (loc_add_ne_null l _ Hcar)]
  try wp_auto
  rw [show typeSize Pgid = 8 from go.typeSize_w64]
  try wp_auto
  by_cases Hbig : sint.Z (W64 ((2 ^ 63 - 1) / 8)) < sint.Z (fpCount v c)
  · rw [decide_eq_true Hbig]
    try wp_auto
    wp_apply wp_AngelicExit
  rw [decide_eq_false Hbig]
  try wp_auto
  rw [ite_eq_right_of_eq_false _ _ (eq_false Hif)]
  have Hoff : sint.Z (W64 16 + fpIdx v * W64 8) = 16 + 8 * uint.Z (fpIdx v) := by
    generalize fpIdx v = x at Hidx ⊢; word
  rw [Hoff]
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
