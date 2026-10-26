/-
`NewTyped[T]()` (`queue.go`): `NewTypedWithConfig(TypedQueueConfig[T]{Name: ""})`. Lean-first.
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

/-- `NewTyped()`: a typed queue (unnamed: no metrics) and its shutdown tokens. -/
abbrev NewTyped.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val #(functions NewTyped [T])) (Val #()))
  {{ (q : Loc) (γ : QNames), RET #q; isTyped (K := K) q γ ∗ shutdownToks γ shutdownPool }}

end spec

end workqueue
end EtcdGrove
end Perennial
