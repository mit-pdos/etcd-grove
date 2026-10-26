/-
`(*Typed[T]).Add(item)` (`queue.go`): marks `item` dirty and queues it unless it is being
processed (then `Done` queues it) or already dirty; ignored once the queue is shutting down
(`QState.add`). Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has

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

/-- `q.Add(item)`: under the lock, the abstract state becomes `QState.add σ item`; nothing is
returned to the caller (who holds no token for `item`: an `Add` of an item being processed only
marks it dirty, so it is handed out again after `Done`). -/
abbrev Typed.Add.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"Add")) (Val #k))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
