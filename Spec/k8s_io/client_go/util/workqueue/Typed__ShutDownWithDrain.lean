/-
`(*Typed[T]).ShutDownWithDrain()` (`queue.go`): `ShutDown`, then waits, under the condition
variable, until no item is being processed (or a later `ShutDown` clears `drain`). Lean-first.
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

/-- `q.ShutDownWithDrain()`, with a shutdown token (given back): afterwards the queue is
shutting down. (It returns only once no item is being processed, or a `ShutDown` ran: a caller
holding a `keyTok` blocks it, as Go's documentation says; liveness is not stated.) -/
abbrev Typed.ShutDownWithDrain.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ ∗
      shutdownToks γ 1 }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"ShutDownWithDrain")) (Val #()))
  {{ RET #(); shutdownLb γ ∗ shutdownToks γ 1 }}

end spec

end workqueue
end EtcdGrove
end Perennial
