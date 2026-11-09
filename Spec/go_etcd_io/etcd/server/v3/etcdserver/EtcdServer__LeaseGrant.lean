/-
## `(*EtcdServer).LeaseGrant(ctx, r)`

**Users.** The gRPC lease handler (`api/v3rpc/lease.go:45`, through `Lessor`), the grpc-proxy's
lease adapter. Snippet: `examples/specreq/etcdserverreq/lease.go` (`ReqGrantThenRevoke`).

**Proof sketch.** While `r.ID == 0`, `r.ID = int64(s.reqIDGen.Next() & (1<<63 - 1))` (`IdUtil.
Generator.Next.spec`; the id's value is unconstrained: a collision with a live lease is W0's
`ErrLeaseExist`, `issues/etcd-lease-id-mask-member-prefix.md`); the span; `requireAuthInfo`
(`requireAuthInfo.spec`: auth enabled and no principal is `ErrUserEmpty`, a refusal, the update given
back); `raftRequest` at `.req (.leaseGrant id' ttl)`: the caller's update is for `.leaseGrant id ttl`
and `Step` of the latter answers the former's commit (`leaseStep`: for `id = 0`, any fresh id
`id'`, and `ErrLeaseExist` for any id), so the update passed on is the caller's, read through that
implication (an update of the wider relation, built by the proof); the type assertion
`resp.(*pb.LeaseGrantResponse)`.

**Changes.** The old spec (`specs-ref`'s `EtcdServer__LeaseGrant.lean`, over the lessor's grant
facts) restated over W0's `leaseStep` and the three outcomes.

**Margin.** The id proposed is not returned in the post beyond the request message's (the reply's
id is the answer's).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.LeaseGrant(ctx, r)`**: the grant of lease `id` (`0`: the server chooses one) for `ttl`, as `Put` (through raft); the request's `ID` is set to the id proposed. -/
def EtcdServer.LeaseGrant.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (id ttl : Int),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"LeaseGrant")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ ClientV3.reqOwn r (DFrac.own 1) (.leaseGrant id ttl))
    iprop(threadTok ∗ ∃ id', ClientV3.reqOwn r (DFrac.own 1) (.leaseGrant id' ttl)) γ who (.leaseGrant id ttl) false (ClientV3.ansReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
