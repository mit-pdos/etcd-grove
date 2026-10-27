/-
`(*waitForPriorityQueue[T]).Pop()` (`delaying_queue.go`): removes the last entry (its index `-1`) and returns it, as an `interface{}`. Lean-first.
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

/-- `pq.Pop()` on entries `ws ++ [a]`: `a`'s entry, now the caller's (index `-1`); the heap `ws`. -/
abbrev waitForPriorityQueue.Pop.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (pq : Loc) (s : GoSlice) (ws : List (Loc × K)) (a : Loc × K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ pq ↦ (s : waitForPriorityQueue K) ∗ wqAt (K := K) s (ws ++ [a]) }}
    (App (Val (pq @!! go.GoType.PointerType (waitForPriorityQueue.ty T) @!! go!"Pop")) (Val #()))
  {{ RET #(interface.mkOk (go.GoType.PointerType (waitFor.ty T)) #a.1 : GoInterface);
      (∃ s' : GoSlice, pq ↦ (s' : waitForPriorityQueue K) ∗ wqAt (K := K) s' ws) ∗ wfAt (K := K) a.1 a.2 (W64 (-1)) }}

end spec

end workqueue
end EtcdGrove
end Perennial
