/-
`waitForPriorityQueue[T].Peek()` (`delaying_queue.go`): `pq[0]`, as an `interface{{}}`. Lean-first.
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

/-- `pq.Peek()` on a non-empty heap: its first entry. -/
abbrev waitForPriorityQueue.Peek.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (s : GoSlice) (a : Loc × K) (ws : List (Loc × K)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ wqAt (K := K) s (a :: ws) }}
    (App (Val (s @!! waitForPriorityQueue.ty T @!! go!"Peek")) (Val #()))
  {{ RET #(interface.mkOk (go.GoType.PointerType (waitFor.ty T)) #a.1 : GoInterface);
      wqAt (K := K) s (a :: ws) }}

end spec

end workqueue
end EtcdGrove
end Perennial
