/-
`(*Typed[T]).Done(item)` (`queue.go`): `item` leaves the processing set; if it was added while
being processed (it is dirty), it is queued again (`QState.done`). Lean-first.

The token is the precondition: `Done(k)` for an item that is not being processed, but dirty
(queued), pushes a second copy of `k` (two `Get`s can then hand `k` out at once:
`issues/k8s-workqueue-done-without-get-duplicates.md`); `QState.wf` would not be preserved.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `q.Done(item)`, with `item`'s token (from the `Get` that returned it), which it consumes:
after it, `item` is no longer being processed (and is queued again if added meanwhile). -/
abbrev Typed.Done.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ ∗
      keyTok γ k }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"Done")) (Val #k))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
