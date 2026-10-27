/-
`waitForPriorityQueue[T].Len()` (`delaying_queue.go`): the slice's length. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs

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

/-- `pq.Len()`: the slice's length. -/
abbrev waitForPriorityQueue.Len.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val (s @!! waitForPriorityQueue.ty T @!! go!"Len")) (Val #()))
  {{ RET #s.len; True }}

end spec

end workqueue
end EtcdGrove
end Perennial
