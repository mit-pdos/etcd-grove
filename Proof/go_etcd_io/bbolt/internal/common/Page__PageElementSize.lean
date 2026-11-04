/-
`(*Page).PageElementSize`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__PageElementSize
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage

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

theorem Page.PageElementSize.wp_proof
    (wp_Page_IsLeafPage : Page.IsLeafPage.spec (GF := GF) (hG := hG)) :
    Page.PageElementSize.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  simp only [LeafPageElementSize, BranchPageElementSize]
  wp_auto
  wp_apply wp_Page_IsLeafPage $$ [$Hl] as Hl
  wp_if_destruct <;> (iapply HΦ; iframe)

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
