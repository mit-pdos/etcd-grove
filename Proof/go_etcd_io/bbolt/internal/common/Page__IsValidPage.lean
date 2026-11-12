/-
`(*Page).IsValidPage`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__IsValidPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsMetaPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Page.IsValidPage.wp_proof
    (wp_Page_IsBranchPage : Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (wp_Page_IsLeafPage : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (wp_Page_IsMetaPage : Page.IsMetaPage.spec (GF := GF) (hG := hG))
    (wp_Page_IsFreelistPage : Page.IsFreelistPage.spec (GF := GF) (hG := hG)) :
    Page.IsValidPage.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  wp_auto
  wp_apply wp_Page_IsBranchPage $$ [$Hl] as Hl
  wp_if_destruct
  · rw [show decide (v.flags' = W16 1 ∨ v.flags' = W16 2 ∨ v.flags' = W16 4 ∨ v.flags' = W16 16) = true by simp_all]
    iapply HΦ; iframe
  wp_apply wp_Page_IsLeafPage $$ [$Hl] as Hl
  wp_if_destruct
  · rw [show decide (v.flags' = W16 1 ∨ v.flags' = W16 2 ∨ v.flags' = W16 4 ∨ v.flags' = W16 16) = true by simp_all]
    iapply HΦ; iframe
  wp_apply wp_Page_IsMetaPage $$ [$Hl] as Hl
  wp_if_destruct
  · rw [show decide (v.flags' = W16 1 ∨ v.flags' = W16 2 ∨ v.flags' = W16 4 ∨ v.flags' = W16 16) = true by simp_all]
    iapply HΦ; iframe
  wp_apply wp_Page_IsFreelistPage $$ [$Hl] as Hl
  rw [show decide (v.flags' = W16 1 ∨ v.flags' = W16 2 ∨ v.flags' = W16 4 ∨ v.flags' = W16 16) = decide (v.flags' = W16 16) by simp_all]
  iapply HΦ; iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
