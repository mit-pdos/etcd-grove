/-
`insert[T](q, knownEntries, entry)` (`delaying_queue.go`): a new item's entry pushed on the heap
and recorded by item; for an item already waiting, its ready time moved earlier if the new one
is (and the heap fixed). Lean-first.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `insert(q, m, entry)` with an entry the caller owns: the heap and the map still agree
(`byDataOk`). -/
abbrev insert.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (pq : Loc) (ws : List (Loc × K))
    (m : Loc) (mm : GMap K Loc) (w : Loc) (wf : waitFor K),
  byDataOk mm ws →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ wqHeap (K := K) pq ws ∗
      m ↦$ mm ∗ wfFields (K := K) w wf }}
    (App (App (App (Val #(functions insert [T])) (Val #pq)) (Val #m)) (Val #w))
  {{ RET #(); ∃ (ws' : List (Loc × K)) (mm' : GMap K Loc),
      wqHeap (K := K) pq ws' ∗ m ↦$ mm' ∗ ⌜byDataOk mm' ws'⌝ }}

end spec

end workqueue
end EtcdGrove
end Perennial
