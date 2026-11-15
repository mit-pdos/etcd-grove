/-
`v3rpc.cancellableContext.Err` (`v3rpc/interceptor.go:297`; k8s 7f-4). Lean-first (no Rocq
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

/-- **`l.Err()`**, by a thread lending its level-`v3rpc.ctxErrLvl` token (returned; with it the
call borrows a reader slot of `l.lock` from the wrapper's pool, Freeze addendum T-f'): some error,
nil or not (a stored reason is returned before the embedded context is cancelled); if the wrapper
was known done before the call (`b`, `ContextClosed`), a non-nil error that is a context error
(`isCtxErr`) or etcd's no-leader error (`noLeaderErr`). -/
abbrev v3rpc.cancellableContext.Err.spec : Prop :=
  ∀ (l : Loc) (c1 : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.ccHandle l c1 cd ∗ levelTok v3rpc.ctxErrLvl ∗
      (if b then context.ContextClosed cd.Done_gn else iprop(True)) }}
    (App (Val (l @!! go.GoType.PointerType v3rpc.cancellableContext.ty @!! go!"Err")) (Val #()))
  {{ (err : GoInterface), RET #err; levelTok v3rpc.ctxErrLvl ∗
      (if b then iprop(⌜err ≠ GoInterface.nil⌝ ∗ (context.isCtxErr err ∨ noLeaderErr err))
        else iprop(True)) }}

end spec

end EtcdGrove
end Perennial
