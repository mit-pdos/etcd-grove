/-
`(*clientv3.lessor).Revoke` (`client/v3/lease.go`).

Users: `concurrency.Session.Close` (`session.go:112`), snippet `clientv3lease/session.go`
(`ReqSessionLifecycle`), `examples/etcd/leaseexpiry`'s `expire_revoke_test`.

Proof sketch: builds `&pb.LeaseRevokeRequest{ID: id}`, `l.remote.LeaseRevoke` (repeatable: the
update persistent), returns the reply converted (`(*LeaseRevokeResponse)(resp)`: `ansReply`'s
`replyOwn _ .leaseRevoke`) or `ContextError`'s error.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__Revoke.lean`: restated over the
model; the update persistent (a resent revoke answers `ErrLeaseNotFound`).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.Revoke(ctx, id)`: `.leaseRevoke id` linearized by the caller's persistent update. -/
def lessor.Revoke.spec : Prop :=
  ∀ (l : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (id : w64),
  CallTriple (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Revoke")) (Val #ctx)) (Val #id))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who ∗ Context.ctxOk ctx) iprop(True) γ who (.leaseRevoke (sint.Z id)) true ansReply

end spec

end ClientV3
end EtcdGrove
end Perennial
