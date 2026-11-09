/-
## `(*EtcdServer).LeaseRevoke(ctx, r)`

**Users.** The gRPC lease handler (`api/v3rpc/lease.go:54`); the lessor's expiry
(`revokeExpiredLeases`, `server.go:882`: the context `authStore.WithRoot(s.ctx)`, principal `root`
when auth is enabled at the call, else the context unchanged (`reqPrin` of 3d's `WithRoot` spec:
`some root` or `none`, mode-dependent), with an update built from W0's `envUpd` (`EnvStep.leaseExpire` for a
live lease's revocation, the identity aborted: every other answer of `Step` leaves the state as it
was); it ignores the reply). Snippet: `examples/specreq/etcdserverreq/lease.go`
(`ReqGrantThenRevoke`, `ReqExpiryRevoke`).

**Proof sketch.** The span, `requireAuthInfo` (a refusal given back), `raftRequest` at `.req
(.leaseRevoke id)`, the type assertion `resp.(*pb.LeaseRevokeResponse)`.

**Changes.** The old spec (`specs-ref`'s `EtcdServer__LeaseRevoke.lean`) restated over W0's
`leaseStep` (the keys attached deleted at one revision, the permission of `checkLeasePuts`).

**Margin.** As `Put`.
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

/-- **`s.LeaseRevoke(ctx, r)`**: the revocation of lease `id`, as `Put` (through raft). -/
def EtcdServer.LeaseRevoke.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac) (id : Int),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"LeaseRevoke")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ ClientV3.reqOwn r dq (.leaseRevoke id))
    iprop(threadTok ∗ ClientV3.reqOwn r dq (.leaseRevoke id)) γ p tls (.leaseRevoke id) false (ClientV3.ansReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
