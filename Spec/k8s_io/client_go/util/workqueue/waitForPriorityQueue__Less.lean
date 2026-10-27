/-
`waitForPriorityQueue[T].Less(i, j)` (`delaying_queue.go`): `pq[i].readyAt.Before(pq[j].readyAt)`. Lean-first.
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

/-- `pq.Less(i, j)`, `i` and `j` in range: some `bool`; the heap unchanged. -/
abbrev waitForPriorityQueue.Less.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (s : GoSlice) (ws : List (Loc × K)) (i j : w64),
  0 ≤ sint.Z i → sint.Z i < ws.length → 0 ≤ sint.Z j → sint.Z j < ws.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ wqAt (K := K) s ws }}
    (App (App (Val (s @!! waitForPriorityQueue.ty T @!! go!"Less")) (Val #i)) (Val #j))
  {{ (b : Bool), RET #b; wqAt (K := K) s ws }}

end spec

end workqueue
end EtcdGrove
end Perennial
