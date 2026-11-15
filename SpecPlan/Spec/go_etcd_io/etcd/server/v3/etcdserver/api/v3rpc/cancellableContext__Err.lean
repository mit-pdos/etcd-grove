/-
`v3rpc.cancellableContext.Err` (`server/etcdserver/api/v3rpc/`).

Users: the stream handlers through the context (`LeaseServer.LeaseKeepAlive`'s `stream.Context().Err()`, 2b's watch).

Proof sketch: the read lock; the stored reason, else the inner context's `Err()` (W0's `Err.spec`).

Changes: new.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `c.Err()`: `nil`, a context's error, or the status a `Cancel` stored. -/
def cancellableContext.Err.spec : Prop :=
  ∀ (c : Loc) (parent : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ cctxAt c parent }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty @!! go!"Err")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ context.isCtxErr err ∨
      ∃ code msg, statusErr err code msg }}

end spec

end V3rpc
end EtcdGrove
end Perennial
