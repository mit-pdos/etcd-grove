/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/isClientCtxErr.lean` over the body of
`isClientCtxErr` (`util.go`; prove-grpcext, 2026-11-20: a trust-boundary axiom while it was names only),
over grpc's `status.FromError` and the returned status's `Code()` and `Message()` (its post), and
`strings.HasPrefix`/`HasSuffix`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Spec.google_golang_org.grpc.status.FromError
public import Spec.strings.HasSuffix

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.isClientCtxErr.wp_proof
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_HasSuffix : EtcdGrove.strings.HasSuffix.spec (GF := GF) (hG := hG)) :
    v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG) := by
  intro ctxErr err
  wp_start as #Hse
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  cases ctxErr with
  | ok ci =>
    wp_auto
    iapply HΦ; itrivial
  | nil =>
    wp_auto
    ihave ⟨%mF, #HmF⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_msg _ $$ Hse
    wp_apply wp_FromError err mF $$ [$Hst $Hse $HmF] as %ev %ok ⟨-, #HCode, #HMsg, -⟩
    cases ok
    · wp_auto
      iapply HΦ; itrivial
    · wp_auto
      wp_apply HCode
      repeat (first
        | (iapply HΦ; itrivial)
        | wp_if_destruct
        | (wp_apply HMsg)
        | (wp_apply _root_.Perennial.strings.wp_HasPrefix $$ [$Hstr])
        | (wp_apply wp_HasSuffix $$ [$Hstr])
        | wp_auto)

end proof

end EtcdGrove
end Perennial
