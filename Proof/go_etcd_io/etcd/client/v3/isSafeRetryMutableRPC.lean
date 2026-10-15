/-
Proof of `Spec/go_etcd_io/etcd/client/v3/isSafeRetryMutableRPC.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.isSafeRetryMutableRPC
public import Spec.google_golang_org.grpc.status.FromError
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem isSafeRetryMutableRPC.wp_proof
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_ErrorDesc : rpctypes.ErrorDesc.spec (GF := GF) (hG := hG)) :
    isSafeRetryMutableRPC.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hse
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_FromError err $$ [$Hst $Hse] as %ev %ok ⟨-, #HCode, -⟩
  cases ok
  · wp_auto
    wp_apply wp_ErrorDesc err $$ [$Hse] as %d -
    wp_if_destruct
    · iapply HΦ; itrivial
    · iapply HΦ; itrivial
  · wp_auto
    wp_apply HCode as %c
    wp_if_destruct
    · wp_apply wp_ErrorDesc err $$ [$Hse] as %d -
      wp_if_destruct
      · iapply HΦ; itrivial
      · iapply HΦ; itrivial
    · iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
