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
it; otherwise `nil` and `ContextError(ctx, err)`. -/
abbrev lessor.Revoke.spec : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse)
    (Q : LeaseRevokeRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseRevoke" Spec ∗ □ ▷ Spec id Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Revoke"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseRevokeRespM, leaseRevokeRespMsg resp m ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err) }}

end spec

end EtcdGrove
end Perennial
