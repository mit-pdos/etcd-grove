/-
`v3rpc.cancellableContext.Cancel` (`server/etcdserver/api/v3rpc/`).

Users: `monitorLeader` (with `ErrGRPCNoLeader`), `newStreamInterceptor` (with `nil`, when the handler returns).

Proof sketch: the write lock, the reason stored, the inner context's `cancel` (W0's `cancelOk`: any number of times, concurrently).

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

/-- `c.Cancel(reason)`: done, with the reason (a status error or `nil`). -/
def cancellableContext.Cancel.spec : Prop :=
  ∀ (c : Loc) (parent reason : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ cctxAt c parent ∗ (⌜reason = GoInterface.nil⌝ ∨ ∃ code msg, statusErr reason code msg) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty @!! go!"Cancel")) (Val #reason))
  {{ RET #(); True }}

end spec

end V3rpc
end EtcdGrove
end Perennial
