/-
`v3rpc.newCancellableContext` (`server/etcdserver/api/v3rpc/`).

Users: `newStreamInterceptor`.

Proof sketch: `context.WithCancel(parent)` (W0's `Context.WithCancel`), a fresh struct with its lock.

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

/-- `newCancellableContext(parent)`: a context over `parent`, cancelable with a reason. -/
def newCancellableContext.spec : Prop :=
  ∀ (parent : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ Context.ctxOk parent }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newCancellableContext)) (Val #parent))
  {{ (c : Loc), RET #c; cctxAt c parent ∗
      Context.ctxOk (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty) #c) ∗
      Context.ctxChild parent (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty) #c) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
