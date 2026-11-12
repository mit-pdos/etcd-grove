/-
`(*queue[T]).Pop()` (`queue.go`): removes the front of the slice FIFO (Go indexes `(*q)[0]`:
it panics on an empty queue, which `Typed`'s callers never pop). Lean-first.
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

/-- `q.Pop()` on a non-empty FIFO: its front. -/
abbrev queue.Pop.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (l : Loc) (k : K) (xs : List K),
  {{ ownFifo (GF := GF) l (k :: xs) }}
    (App (Val (l @!! go.GoType.PointerType (queue.ty T) @!! go!"Pop")) (Val #()))
  {{ RET #k; ownFifo (GF := GF) l xs }}

end spec

end workqueue
end EtcdGrove
end Perennial
