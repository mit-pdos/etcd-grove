module
public import Spec.go_etcd_io.bbolt.internal.common.NewPage
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

theorem NewPage.wp_proof : NewPage.spec (GF := GF) (hG := hG) := by
  intro id flags count overflow
  wp_start
  wp_auto
  wp_apply wp_alloc as %l Hl
  try wp_auto
  iapply HΦ; iexact Hl

end proof

end bbolt
end EtcdGrove
end Perennial
