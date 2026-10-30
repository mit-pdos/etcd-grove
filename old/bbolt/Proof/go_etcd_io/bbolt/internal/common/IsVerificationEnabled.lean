module
public import Spec.go_etcd_io.bbolt.internal.common.IsVerificationEnabled
public import Spec.go_etcd_io.bbolt.internal.common.getEnvVerify
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

theorem IsVerificationEnabled.wp_proof (hE : getEnvVerify.spec (GF := GF) (hG := hG))
    (hL : strings.ToLower.spec (GF := GF) (hG := hG)) :
    IsVerificationEnabled.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  wp_apply hE as %e _
  try wp_auto
  wp_if_destruct
  · iapply HΦ; itrivial
  try wp_auto
  wp_apply hL as %u _
  try wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
