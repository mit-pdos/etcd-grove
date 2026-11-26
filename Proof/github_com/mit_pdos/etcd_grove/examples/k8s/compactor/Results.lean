/-
**Kubernetes' compactor example's results** (`examples/k8s/compactor`; K4 of
`notes/k8s-compactor-plan.md`), restated, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8s_compactor_Main`** (`MainLinked.lean`): `Main` does not panic. From `isPkgInit`, the right
  to listen on the client address, the main thread's token, the member's start premises
  (`etcdstart.premises`), a fresh data directory and the compactor registry's authority with no
  endpoint claimed (`regAuth ∅`), under the named hypothesis of
  `clock.RealClock.After`.
* **`k8s_compactor_MainPartition`** (`MainLinked.lean`; K6): `MainPartition(k, sched)` does not panic.
  From `isPkgInit`, the right to listen on the nine addresses of `clusterCfg` (the members' peer
  addresses with their HTTP rights), the schedule read-only (any steps), the main thread's token,
  the cluster's premises (`cluster3.premises`), fresh data directories and `regAuth ∅`, under the
  named hypothesis of `clock.RealClock.After`.

**The closed theorems retired (2026-11-20, the user's decision D3 of `notes/k8s-unified-scope.md`).**
Its closed theorems `k8s_compactor_safe` and `k8s_compactor_partition_safe` (with
`Adequacy.lean`, `TopLevelDefs.lean` and the `TopLevelRobustness.lean` pair) are gone: the one closed Kubernetes theorem `k8s_safe` (`examples/k8s/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/all/Results.lean`) runs `MainPartition` beside the
store driver's in one process; the function triples here stay (`k8s_compactor_MainPartition` is its callee).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainLinked

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `k8s_compactor.wp_Main`). -/
theorem k8s_compactor_Main
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_compactor.Main.spec (GF := GF) (hG := hG) :=
  k8s_compactor.wp_Main h_After

/-- **`MainPartition` does not panic** (`MainLinked.lean`'s `k8s_compactor.wp_MainPartition`). -/
theorem k8s_compactor_MainPartition
    [go_etcd_io.etcd.cache.v3.Assumptions]
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_compactor.MainPartition.spec (GF := GF) (hG := hG) :=
  k8s_compactor.wp_MainPartition h_After

end results

#print axioms k8s_compactor_Main
#print axioms k8s_compactor_MainPartition

end EtcdGrove
end Perennial
