module
public import Spec.go_etcd_io.bbolt.internal.common.getEnvVerify
public import Spec.os.Getenv
public import Spec.strings.ToLower

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

theorem getEnvVerify.wp_proof (hG' : os.Getenv.spec (GF := GF) (hG := hG))
    (hL : strings.ToLower.spec (GF := GF) (hG := hG)) :
    getEnvVerify.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply hG' as %s _
  wp_apply hL as %t _
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
