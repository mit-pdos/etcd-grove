/-
`(*clientv3.lessor).Grant` (`client/v3/lease.go`).

Users: `concurrency.NewSession` (`session.go:50`: the session's lease, `resp.ID`), Kubernetes' lease
manager (`lease_manager.go:109`: `lcr.ID` for the events' TTL keys), recipes and leasing through
sessions, `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}`; snippets `clientv3lease/grant.go`
(`ReqGrantThenPut`, `ReqGrantTTL`), `clientv3lease/session.go`.

Proof sketch: builds `&pb.LeaseGrantRequest{TTL: ttl}` (`reqOwn _ _ (.leaseGrant 0 ttl)`), calls
`l.remote.LeaseGrant(ctx, r, l.callOpts...)` (`lessorHandle`: `remoteLeaseAt`, `remoteLeaseAt_call`:
repeatable, so the caller's update is persistent: the interceptor may resend after an applied
attempt); on success copies `GetHeader()`, `ID`, `TTL`, `Error` into a fresh `LeaseGrantResponse`
(`leaseGrantReply`: the reply message's fields, 3h's unfold of `replyOwn _ (.leaseGrant id ttl)`);
on an error `ContextError` (W0).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__Grant.lean` (a grant on one server's
lessor, an exclusive update, no auth): restated over the model (`Step who (.leaseGrant 0 ttl)`), the
update persistent (the retry policy: the old spec's exclusive update was unsound against a resent
grant), any principal, the answer's id and TTL in the reply.

Margin: the reply's header and `Error` field are not modelled.
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

/-- `l.Grant(ctx, ttl)`: a lease granted (`.leaseGrant 0 ttl`, the id the server's), linearized
by the caller's **persistent** update (the RPC is resent: an earlier attempt may have granted another
lease), or an error that settles nothing. -/
def lessor.Grant.spec : Prop :=
  ∀ (l : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (ttl : w64),
  CallTriple (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant")) (Val #ctx)) (Val #ttl))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who ∗ Context.ctxOk ctx) iprop(True) γ who (.leaseGrant 0 (sint.Z ttl)) true leaseGrantReply

end spec

end ClientV3
end EtcdGrove
end Perennial
