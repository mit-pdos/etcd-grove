/-
`v3rpc.healthNotifier.startServe` (`server/etcdserver/api/v3rpc/`).

Users: `newHealthNotifier`, `defragFinished`.

Proof sketch: the logger (`Zap`'s, W0) with the status's `String()` (the generated enum stringer), `hs.SetServingStatus` (grpc's health server).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/healthNotifier__startServe.lean`.

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

/-- `hc.startServe()`: returns. -/
def healthNotifier.startServe.spec : Prop :=
  ∀ (hc : Loc) (n : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ notifierAt n ∗ ⌜n = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.healthNotifier.ty) #hc⌝ }}
    (App (Val (hc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.healthNotifier.ty @!! go!"startServe")) (Val #()))
  {{ RET #(); True }}

end spec

end V3rpc
end EtcdGrove
end Perennial
