/-
`(*Typed[T]).ShuttingDown()` (`queue.go`): the shutting-down flag, under the lock. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

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

/-- `q.ShuttingDown()`: `true` only once the queue is shutting down (`shutdownLb`, persistent;
`false` says nothing: a `ShutDown` may follow at once). -/
abbrev Typed.ShuttingDown.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"ShuttingDown")) (Val #()))
  {{ (b : Bool), RET #b; if b then shutdownLb γ else True }}

end spec

end workqueue
end EtcdGrove
end Perennial
