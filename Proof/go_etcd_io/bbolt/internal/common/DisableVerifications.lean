module
public import Spec.go_etcd_io.bbolt.internal.common.DisableVerifications
public import Spec.go_etcd_io.bbolt.internal.common.getEnvVerify
public import Spec.os.Setenv
public import Spec.os.Unsetenv

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

theorem DisableVerifications.wp_proof (hE : getEnvVerify.spec (GF := GF) (hG := hG))
    (hS : os.Setenv.spec (GF := GF) (hG := hG)) (hU : os.Unsetenv.spec (GF := GF) (hG := hG)) :
    DisableVerifications.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply hE as %e _
  try wp_auto
  ipersist previousEnv
  wp_apply hU as %err _
  try wp_auto
  rw [recv_eq_func_mk]
  iapply HΦ
  imodintro
  wp_auto
  wp_apply hS as %err' _
  try wp_auto
  itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
