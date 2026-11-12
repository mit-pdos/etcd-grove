/-
`v3rpc.cancellableContext.Cancel` (`v3rpc/interceptor.go:288`; k8s 7f-4). Lean-first (no Rocq
counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvCancellable.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCancellable

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`l.Cancel(reason)`**, by anyone (the writer's guard, no token), with `reason` `nil` or
`rpctypes.ErrGRPCNoLeader`'s value (the program's two callers: the interceptor's `defer` and
`monitorLeader`): stores the reason under the write lock and cancels the embedded `WithCancel`
child, so the wrapper is done (`ContextClosed`). -/
abbrev v3rpc.cancellableContext.Cancel.spec : Prop :=
  ∀ (l : Loc) (c1 : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (reason : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.ccHandle l c1 cd ∗ (⌜reason = GoInterface.nil⌝ ∨ noLeaderErr reason) }}
    (App (Val (l @!! go.GoType.PointerType v3rpc.cancellableContext.ty @!! go!"Cancel"))
      (Val #reason))
  {{ RET #(); context.ContextClosed cd.Done_gn }}

end spec

end EtcdGrove
end Perennial
