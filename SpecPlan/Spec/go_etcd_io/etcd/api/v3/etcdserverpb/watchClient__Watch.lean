/-
`(*watchClient).Watch` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the streaming stub.

Users: the client's watcher (1b: `watchGRPCStream.openWatchClient` through `remoteWatchAt_watch`).
Proof sketch: `StaticMethod()`, `append`, the stream descriptor `&Watch_ServiceDesc.Streams[0]`
(`descStreams_init`), the connection's `NewStream` (the caller's `streamStubWP`), the wrapper
`&grpc.GenericClientStream[...]{ClientStream: stream}` on success.
Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/watchClient__Watch.lean`: over grpc's stream halves (2a) instead of the old `StreamMsg` models; WP form.
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

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

/-- `c.Watch(ctx, opts...)`: the connection's `NewStream` of `/etcdserverpb.Watch/Watch`, wrapped (WP
form). -/
def watchClient.Watch.spec : Prop :=
  ∀ (c : Loc) (cc ctx : GoInterface) (opts : GoSlice) (dq : DFrac) (os : List GoInterface)
    (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ stubAt etcdserverpb.watchClient c cc ∗ opts ↦*{dq} os ∗
    (∀ sd : Loc, opts ↦*{dq} os -∗
      streamStubWP (Req := etcdserverpb.WatchRequest) (Res := etcdserverpb.WatchResponse) cc sd
        etcdserverpb.Watch_Watch_FullMethodName etcdserverpb.WatchRequest.ty etcdserverpb.WatchResponse.ty ctx os Ψ) ⊢
  WP (App (App (Val (c @!! go.GoType.PointerType etcdserverpb.watchClient.ty @!! go!"Watch")) (Val #ctx))
    (Val #opts)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
