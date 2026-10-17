/-
Proof of `Spec/go_etcd_io/etcd/client/v3/isContextError.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.isContextError
public import Spec.google_golang_org.grpc.status.Code

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

theorem isContextError.wp_proof
    (wp_Code : status.Code.spec (GF := GF) (hG := hG)) :
    isContextError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hse
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Code err $$ [$Hst $Hse] as %c1 -
  wp_if_destruct
  · iapply HΦ; itrivial
  · wp_apply wp_Code err $$ [$Hst $Hse] as %c2 -
    iapply HΦ; itrivial

/-- (etcd-io/etcd#21739, pr-verify) No callee spec: `ctxCodeErr` is `status.Code`'s result. -/
theorem isContextError.wp_proof_ctx :
    isContextError.spec_ctx (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hce
  wp_auto
  iunfold ctxCodeErr at Hce
  icases Hce with (#H4 | #H1)
  all_goals (try iunfold statusCodeIs at H4)
  all_goals (try iunfold statusCodeIs at H1)
  · wp_bind (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
    iapply H4
    inext
    wp_auto
    iapply HΦ; itrivial
  · wp_bind (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
    iapply H1
    inext
    wp_auto
    wp_bind (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
    iapply H1
    inext
    wp_auto
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
