/-
`(*kVClient).RangeStream` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the server-streaming stub.

Users: the client's `retryKVClient.RangeStream` (`client/v3/retry.go:111-112`; 1c's `remoteKVAt_methods`' `RangeStreamTriple`, which `NewKVClient.spec`'s proof needs), Kubernetes' `store.go:951` through the client's `GetStream`. Snippet: `examples/specreq/v3rpc/kv.go` (`ReqRangeStream`).
Proof sketch: `StaticMethod()`, `append`, the stream descriptor `&KV_ServiceDesc.Streams[0]`
(the caller's `sd`), the connection's `NewStream` (the caller's `serverStreamStubWP`), the wrapper
`&grpc.GenericClientStream[...]{ClientStream: stream}` (persisted: grpc's `genCliAt`, its intended
realization), then `x.ClientStream.SendMsg(in)` and `x.ClientStream.CloseSend()`, each error
returned with a `nil` stream. Blocked: the body is untranslated (names only in `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`): the proof waits for its translation (open question 7.4).
Changes: verify-round: new (A6 completeness F1), in the form of the translated streaming stubs
(`leaseClient.LeaseKeepAlive.spec`); the wrapper is grpc's `genCliAt` (its message types have no
translated Lean type to state the wrapper's points-to at).
Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.StreamShapes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `c.RangeStream(ctx, in, opts...)`: the connection's `NewStream` of `/etcdserverpb.KV/RangeStream`, the request
sent and the sending half closed (WP form). -/
def kVClient.RangeStream.spec : Prop :=
  ∀ (c : Loc) (cc ctx : GoInterface) (q : Loc) (opts : GoSlice) (dq : DFrac) (os : List GoInterface)
    (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ stubAt etcdserverpb.kVClient c cc ∗ opts ↦*{dq} os ∗
    (∀ sd : Loc, opts ↦*{dq} os -∗
      serverStreamStubWP cc sd etcdserverpb.KV_RangeStream_FullMethodName etcdserverpb.RangeRequest.ty etcdserverpb.RangeStreamResponse.ty
        ctx q os Ψ) ⊢
  WP (App (App (App (Val (c @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"RangeStream")) (Val #ctx)) (Val #q))
    (Val #opts)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
