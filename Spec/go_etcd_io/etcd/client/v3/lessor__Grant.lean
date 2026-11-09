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
update persistent (the retry policy; the old spec's `□ ▷ Spec` registration was per server, not a
client's update), the principal per call, the answer's id and TTL in the reply, and through one
member the lease table it created (`leaseViewLb`, W0's round 3).

verify-round (A2-provability L2): the per-member clause (`via`) now has a source: `leaseViaPre`'s
`leaseOf v c ∗ clientVia c ep` gives, through `lessorHandle`'s realization, `remoteVia` of the remote
(`NewLeaseFromLeaseClient`'s premise), and `remoteLeaseAt_call` at `V = remoteVia remote` gives the
answer's `viaFact` (from 2a's `AttemptTriple` through `uiOk_call`); a lease read's fact holds for an
answer of the lessor (`leaseAnsRes`), not for a refusal.

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
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  Lease.GrantTriple (fun s => l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! s) (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
