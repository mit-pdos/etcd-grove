module
public import Spec.go_etcd_io.bbolt.internal.common.Page__Typ
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

theorem Page.Typ.wp_proof
    (hB : Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hL : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hM : Page.IsMetaPage.spec (GF := GF) (hG := hG))
    (hF : Page.IsFreelistPage.spec (GF := GF) (hG := hG)) :
    Page.Typ.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  wp_auto
  wp_apply hB $$ [$Hl] as Hl
  wp_if_destruct
  · iapply HΦ; iframe; ipureintro; intro n hn; simp_all [pageTypName]
  try wp_auto
  wp_apply hL $$ [$Hl] as Hl
  wp_if_destruct
  · iapply HΦ; iframe; ipureintro; intro n hn; simp_all [pageTypName]
  try wp_auto
  wp_apply hM $$ [$Hl] as Hl
  wp_if_destruct
  · iapply HΦ; iframe; ipureintro; intro n hn; simp_all [pageTypName]
  try wp_auto
  wp_apply hF $$ [$Hl] as Hl
  wp_if_destruct
  · iapply HΦ; iframe; ipureintro; intro n hn; simp_all [pageTypName]
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply fmt.wp_Sprintf as %s _
  iapply HΦ; iframe; ipureintro; intro n hn; simp_all [pageTypName]

end proof

end bbolt
end EtcdGrove
end Perennial
