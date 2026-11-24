/-
`(*clientv3.lessor).Revoke(ctx, id)` (`client/v3/lease.go`; item 1, the client lease). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.Revoke(ctx, id)` on a `*lessor` over a connection to `addr` (`lessorRemoteAt`), for a spec
`Spec` registered for `LeaseRevoke` and the caller's `Q`: the request `{ID: id}` through the retry
lease client; on success the reply itself (`(*LeaseRevokeResponse)(resp)`, read-only) with `Q` of
it; otherwise `nil` and `ContextError(ctx, err)`. (Auth-lease S4, Freeze §2.2) Over the connection `conn` (`lessorRemoteAtC`), metadata-indexed: the
spec at every metadata an attempt may deliver (`attemptPre`); the old form is the new one at
`GrpcSpec.md` (`attemptPre_md`, `isGrpcRpcs_md`, `lessorRemoteAt_conn`). -/
abbrev lessor.Revoke.spec : Prop :=
  ∀ (l conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse)
    (Q : LeaseRevokeRespM → IProp GF) (ctx : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (id : w64),
  {{ levelTok 0 ∗ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAtC l conn addr ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.Lease/LeaseRevoke" Spec ∗
      metadata.outMD ctx om ∗ □ ▷ attemptPre conn om Spec id Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Revoke"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseRevokeRespM, leaseRevokeRespMsg resp m ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err)) }}

end spec

end EtcdGrove
end Perennial
