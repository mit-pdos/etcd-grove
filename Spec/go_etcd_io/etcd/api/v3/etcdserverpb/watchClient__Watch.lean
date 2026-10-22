/-
`(*etcdserverpb.watchClient).Watch(ctx, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the
generated Watch stub; the watch slice's unit W-W). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/google_golang_org/grpc/InvGrpcStream.lean` and
`server/v3/etcdserver/api/v3rpc/InvWatchStream.lean` (the watch messages, the stub, the
client's end of a watch stream).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Watch(ctx, opts...)` on a stub on a connection to the servers at `addrs` (`watchStubAt`,
`grpcConn` with no default call options), for the stream specification and the client's content
each server registered for the method (`isGrpcStreams`: per address, D30, 2026-10-22; until then
one address): `NewStream` of `"/etcdserverpb.Watch/Watch"` with `grpc.StaticMethod()` before the
options and the service's first `StreamDesc` (`watchDescOk`), wrapped in a
`GenericClientStream[WatchRequest, WatchResponse]`: the client end of a fresh watch stream at some
address `a` of `addrs` (`cliWatchStreamIs`, both tokens at `[]`, `a`'s content and stream
specification `Spec a γ Dn`), or a `nil` stream and a client error. -/
abbrev watchClient.Watch.spec : Prop :=
  ∀ (wc conn : Loc) (addrs : List GoString) (ics : List GoFunc)
    (Up : GoString → Nat → v3rpc.WatchReqM → IProp GF)
    (Spec : GoString → StreamSpec (GF := GF) v3rpc.pbWatchResponse) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      v3rpc.watchStubAt wc conn ∗ grpcConn conn addrs ics [] ∗
      isGrpcStreams (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) addrs
        go!"/etcdserverpb.Watch/Watch" Up Spec ∗
      v3rpc.watchDescOk ∗ ctxOk ctx cd ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (Val (wc @!! go.GoType.PointerType etcdserverpb.watchClient.ty @!! go!"Watch"))
      (Val #(GoInterface.ok ctx))) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (a : GoString) (γ : StreamNames)
          (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF)),
        ⌜a ∈ addrs⌝ ∗ v3rpc.cliWatchStreamIs cs γ (Up a) Dn cd' ∗
        cliSendTok (Req := v3rpc.pbWatchRequest) γ [] ∗
        cliRecvTok (Rep := v3rpc.pbWatchResponse) γ [] ∗ Spec a γ Dn) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err) }}

end spec

end EtcdGrove
end Perennial
