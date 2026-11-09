/-
## `(*EtcdServer).DeleteRange(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:104`, after `checkDeleteRequest`), the
grpc-proxy's adapter. Snippet: `examples/specreq/etcdserverreq/kv.go` (`ReqDeleteThenRange`).

**Proof sketch.** As `Put.spec`: the span, `raftRequest` at `.req (.deleteRange d)`, the type
assertion `resp.(*pb.DeleteRangeResponse)` (`respTy`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__DeleteRange.lean`, over `KVState` and
`kvOpStep`) restated as `Put`'s (see `EtcdServer__Put.lean`).

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

/-- **`s.DeleteRange(ctx, r)`**: the delete `d`, as `Put`. -/
def EtcdServer.DeleteRange.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (dq : DFrac) (d : DeleteReq),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"DeleteRange")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ deleteReqOwn r dq d)
    iprop(threadTok ∗ deleteReqOwn r dq d) γ who (.deleteRange d) false (ClientV3.deleteReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
