/-
## `(*EtcdServer).AuthDisable(ctx, r)`

**Users.** The gRPC auth handler (`api/v3rpc/auth.go`, `AuthServer.AuthDisable` through
`Authenticator`), etcdctl and the client's `Auth` API (1c). Snippet:
`examples/specreq/etcdserverreq/auth.go`.

**Proof sketch.** `raftRequest(ctx, &pb.InternalRaftRequest{...: r})` (`raftRequest.spec` at `.req (.authDisable)`, the message wrapped and given back, 3h; the apply's auth store answers by W0's `authStep`, the admin check at the committed state, 3d), then the type assertion to `*pb.Auth...Response` (`respTy`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__AuthDisable.lean`, the auth plan's A3: one per mode,
then merged, over the auth component's predicates) restated over W0's `authStep` and the three
outcomes; auth on and off are states of the model.

**Margin.** As `Put`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

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

/-- **`s.AuthDisable(ctx, r)`**: disables auth, as `Put`. -/
def EtcdServer.AuthDisable.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"AuthDisable")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ ClientV3.reqOwn r dq (.authDisable))
    iprop(srvGate s q ∗ threadTok ∗ ClientV3.reqOwn r dq (.authDisable)) γ p tls (.authDisable) false (ClientV3.ansReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
