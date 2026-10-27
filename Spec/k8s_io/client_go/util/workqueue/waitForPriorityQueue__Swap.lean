/-
`waitForPriorityQueue[T].Swap(i, j)` (`delaying_queue.go`): swaps the two entries and their indices. Lean-first; the proof is the lessor's queue's (`lease.LeaseQueue.Swap`), adapted.
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

/-- `pq.Swap(i, j)`, `i` and `j` in range: the entries swapped, each at its new index. -/
abbrev waitForPriorityQueue.Swap.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (s : GoSlice) (ws : List (Loc × K)) (i j : w64),
  0 ≤ sint.Z i → sint.Z i < ws.length → 0 ≤ sint.Z j → sint.Z j < ws.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ wqAt (K := K) s ws }}
    (App (App (Val (s @!! waitForPriorityQueue.ty T @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); wqAt (K := K) s (lease.listSwap ws (sint.nat i) (sint.nat j)) }}

end spec

end workqueue
end EtcdGrove
end Perennial
