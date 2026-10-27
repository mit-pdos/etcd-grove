/-
`(*waitForPriorityQueue[T]).Push(x)` (`delaying_queue.go`): the entry `x.(*waitFor[T])` appended, at its index. Lean-first; the lessor's queue's (`lease.LeaseQueue.Push`), adapted.
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

/-- `pq.Push(x)` of an entry the caller owns: appended, at its index. -/
abbrev waitForPriorityQueue.Push.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (pq : Loc) (s : GoSlice) (ws : List (Loc × K)) (w : Loc) (k : K) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ pq ↦ (s : waitForPriorityQueue K) ∗ wqAt (K := K) s ws ∗ wfAt (K := K) w k i }}
    (App (Val (pq @!! go.GoType.PointerType (waitForPriorityQueue.ty T) @!! go!"Push"))
      (Val #(interface.mkOk (go.GoType.PointerType (waitFor.ty T)) #w : GoInterface)))
  {{ RET #(); ∃ s' : GoSlice, pq ↦ (s' : waitForPriorityQueue K) ∗ wqAt (K := K) s' (ws ++ [(w, k)]) }}

end spec

end workqueue
end EtcdGrove
end Perennial
