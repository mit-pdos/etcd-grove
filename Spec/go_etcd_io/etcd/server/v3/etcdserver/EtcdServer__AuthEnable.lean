/-
## `(*EtcdServer).AuthEnable(ctx, r)`

**Users.** The gRPC auth handler (`api/v3rpc/auth.go`, `AuthServer.AuthEnable` through
`Authenticator`), etcdctl and the client's `Auth` API (1c). Snippet:
`examples/specreq/etcdserverreq/auth.go`.

**Proof sketch.** `raftRequest(ctx, &pb.InternalRaftRequest{...: r})` (`raftRequest.spec`
at `.req (.authEnable)`: the apply's auth store answers by W0's `authStep`, the admin check at the
committed state (3d)), then the type assertion to `*pb.AuthEnableResponse`
(`respTy`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__AuthEnable.lean`, the auth plan's A3: one per mode,
then merged, over the auth component's predicates) restated over W0's `authStep` and the three
outcomes; auth on and off are states of the model.

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

/-- **`s.AuthEnable(ctx, r)`**: enables auth, as `Put`. -/
def EtcdServer.AuthEnable.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (dq : DFrac),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"AuthEnable")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ ClientV3.reqOwn r dq (.authEnable))
    iprop(threadTok ∗ ClientV3.reqOwn r dq (.authEnable)) γ who (.authEnable) false (ClientV3.ansReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
