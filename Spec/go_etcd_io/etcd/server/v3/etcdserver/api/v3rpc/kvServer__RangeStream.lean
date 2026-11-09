/-
`kvServer.RangeStream(r, rs)` (`key.go:61`).

Users: grpc's run of `/etcdserverpb.KV/RangeStream` (the generated `_KV_RangeStream_Handler`, 3h:
it receives the one request, `RecvMsg`, then calls this with the stream wrapped as a
`KV_RangeStreamServer`); W0's `RemoteKV.RangeStreamTriple` and `wireStreamAt_recv`
(`examples/specreq/clientv3kv/stream.go`).

Proof sketch: `checkRangeStreamRequest` (`checkRangeStreamRequest.spec`): a validation error is
fired as the model's answer (`kvStep`'s range disjuncts), a custom order or revision filter is
`Unimplemented` (a status that settles nothing: `fin`'s `indefMsg`); then `s.kv.RangeStream(r,
&headerFillingRangeStream{rs, &s.hdr})` (2c's `EtcdServer.RangeStream.spec` over its send end
`rsSink w γ who tls r []`, which this batch realizes from grpc's `srvSend` of the wrapper:
`rsSink_intro`; each chunk recorded `rsChunk g j m`); at its return the update's `Q` with
`streamMatches` of the chunks (or a linearized error, `ErrCompacted`, or one settling nothing),
which `rsSink_out` turns into the run's `streamOut`; the error through `togRPCError`.

Changes: new.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.RangeStream(r, rs)` of a run of `/etcdserverpb.KV/RangeStream`: the received request with its
`up` resource, the stream's send half; returns with `streamOut`. -/
def kvServer.RangeStream.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (r : Loc) (c : Content) (rs : GoInterface) (g : StreamName) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ kvServerAt p s γ ∗ threadTok ∗ msgAt go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty r (DFrac.own 1) c ∗
      (rangeStreamSpec γ).up g md 0 c ∗ (∃ ctx, srvCtxOf rs ctx md) ∗ srvRecv rs g (rangeStreamSpec γ) md 1 ∗
      srvSend rs g (rangeStreamSpec γ) md 0 }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"RangeStream")) (Val #r))
      (Val #rs))
  {{ (err : GoInterface), RET #err; threadTok ∗ streamOut rs g (rangeStreamSpec γ) md err }}

end spec

end V3rpc
end EtcdGrove
end Perennial
