/-
`(*Typed[T]).Len()` (`queue.go`): the FIFO's length, under the lock ("for informational purposes
only"). Lean-first.
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

/-- `q.Len()`: some non-negative `int` (the FIFO's length at the time). -/
abbrev Typed.Len.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"Len")) (Val #()))
  {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ }}

end spec

end workqueue
end EtcdGrove
end Perennial
