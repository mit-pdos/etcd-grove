/-
`(*queue[T]).Len()` (`queue.go`): the slice FIFO's length. Lean-first.
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

/-- `q.Len()`: the number of items. -/
abbrev queue.Len.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (l : Loc) (xs : List K),
  {{ ownFifo (GF := GF) l xs }}
    (App (Val (l @!! go.GoType.PointerType (queue.ty T) @!! go!"Len")) (Val #()))
  {{ RET #(W64 xs.length); ownFifo (GF := GF) l xs }}

end spec

end workqueue
end EtcdGrove
end Perennial
