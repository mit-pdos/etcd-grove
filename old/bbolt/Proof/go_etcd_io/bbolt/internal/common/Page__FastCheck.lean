module
public import Spec.go_etcd_io.bbolt.internal.common.Page__FastCheck
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

theorem Page.FastCheck.wp_proof (hV : Page.IsValidPage.spec (GF := GF) (hG := hG)) :
    Page.FastCheck.spec (GF := GF) (hG := hG) := by
  intro l v dq id Hid Hvalid
  wp_start as Hl
  wp_auto
  rw [decide_eq_true Hid]
  try wp_auto
  wp_apply hV $$ [$Hl] as Hl
  rw [decide_eq_true Hvalid]
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
