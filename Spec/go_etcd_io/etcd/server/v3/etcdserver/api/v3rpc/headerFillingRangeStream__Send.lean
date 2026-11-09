/-
`v3rpc.headerFillingRangeStream.Send` (`server/etcdserver/api/v3rpc/`).

Users: 2c's `EtcdServer.RangeStream` (through `rsSink`'s send law, which this spec realizes).

Proof sketch: `header.fillWithoutRevision.spec` on the chunk's header if it has one; the wrapped stream's `Send` (3h's typed wrapper over `Grpc.srvSend_send`), the chunk recorded (`rsChunk_ids`: the ids filled change no recorded field).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/headerFillingRangeStream__Send.lean`.

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

/-- `w.Send(resp)` of the `j`-th chunk `m` (recorded): sent with the header's ids filled, or an
error grpc made itself. -/
def headerFillingRangeStream.Send.spec : Prop :=
  ∀ (w : Loc) (rs : GoInterface) (hp s : Loc) (γ : Cluster) (g : StreamName) (md : MD) (j : Nat)
    (resp : Loc) (c : Content) (m : RangeRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ hfAt w rs hp s γ ∗ srvSend rs g (rangeStreamSpec γ) md j ∗
      msgAt go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse.ty resp (DFrac.own 1) c ∗ ⌜chunkModels c m⌝ ∗ rsChunk g j m }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.headerFillingRangeStream.ty @!! go!"Send")) (Val #resp))
  {{ (err : GoInterface), RET #err; ∃ c', msgAt go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse.ty resp (DFrac.own 1) c' ∗
      ((⌜err = GoInterface.nil⌝ ∗ srvSend rs g (rangeStreamSpec γ) md (j + 1)) ∨
       (ownErr err ∗ srvSend rs g (rangeStreamSpec γ) md j)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
