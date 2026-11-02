module
public import Spec.go_etcd_io.bbolt.internal.common.EnableAllVerifications
public import Spec.go_etcd_io.bbolt.internal.common.EnableVerifications

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

theorem EnableAllVerifications.wp_proof (hE : EnableVerifications.spec (GF := GF) (hG := hG)) :
    EnableAllVerifications.spec (GF := GF) (hG := hG) := by
  wp_start
  try wp_auto
  wp_apply hE as %r #Hr
  iapply HΦ $$ Hr

end proof

end bbolt
end EtcdGrove
end Perennial
