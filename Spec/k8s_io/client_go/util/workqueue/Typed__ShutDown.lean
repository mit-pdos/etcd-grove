/-
`(*Typed[T]).ShutDown()` (`queue.go`): closes `stopCh` once (`stopOnce`), sets the
shutting-down flag (no new items are taken; workers drain the FIFO, then `Get` reports the
shutdown) and wakes every waiter; then waits for the queue's goroutines (`wg`: none, without
metrics). Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
public import Proof.k8s_io.client_go.util.workqueue.WaitGroup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `q.ShutDown()`, with a shutdown token (given back): afterwards the queue is shutting down
(`shutdownLb`). Any number may run, concurrently with everything else. -/
abbrev Typed.ShutDown.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ ∗
      shutdownToks γ 1 }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"ShutDown")) (Val #()))
  {{ RET #(); shutdownLb γ ∗ shutdownToks γ 1 }}

end spec

end workqueue
end EtcdGrove
end Perennial
