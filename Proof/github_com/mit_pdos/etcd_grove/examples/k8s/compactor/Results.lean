/-
**Kubernetes' compactor example's results** (`examples/k8s/compactor`; K4 of
`notes/k8s-compactor-plan.md`), restated, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8s_compactor_Main`** (`MainLinked.lean`): `Main` does not panic. From `isPkgInit`, the right
  to listen on the client address, the main thread's token, the member's start premises
  (`etcdstart.premises`), a fresh WAL directory and the compactor registry's authority with no
  endpoint claimed (`regAuth ∅`), under the named hypothesis of
  `clock.RealClock.After`.
* **`k8s_compactor_safe`** (`Adequacy.lean`'s `k8s_compactor_adequate`): the closed theorem. Every
  real execution of `n` steps of the example's initialization followed by `Main()`, from a fresh state
  with one thread, has no stuck thread, no thread ended in a panic (no API server's check, no
  compactor round), and the main thread's result, if any, is `#()`.
* **`k8s_compactor_MainPartition`** (`MainLinked.lean`; K6): `MainPartition(sched)` does not panic.
  From `isPkgInit`, the right to listen on the nine addresses of `clusterCfg` (the members' peer
  addresses with their HTTP rights), the schedule read-only (any steps), the main thread's token,
  the cluster's premises (`cluster3.premises`), fresh WAL directories and `regAuth ∅`, under the
  named hypothesis of `clock.RealClock.After`.
* **`k8s_compactor_partition_safe`** (`Adequacy.lean`'s `k8s_compactor_partition_adequate`; K6): the
  closed theorem of the example's initialization followed by `MainPartition(sched)`, the schedule
  built as a slice literal, for every list of steps: three members in compaction mode under
  partitions, the same guarantee as `k8s_compactor_safe`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Adequacy

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
theorem k8s_compactor_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_compactor.Main.spec (GF := GF) (hG := hG) :=
  k8s_compactor.wp_Main h_After

/-- **`MainPartition` does not panic** (`MainLinked.lean`'s `k8s_compactor.wp_MainPartition`). -/
theorem k8s_compactor_MainPartition [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_compactor.MainPartition.spec (GF := GF) (hG := hG) :=
  k8s_compactor.wp_MainPartition h_After

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The compactor example is safe, in the operational semantics** (`k8s_compactor_adequate`, see
the file header and `Adequacy.lean`). -/
theorem k8s_compactor_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextReadErrs (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextErrsClient (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcdstart.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed k8scompactorProgram k8scompactorNames)
    (HAs : addrsUnclaimed k8scompactorProgram [go!"127.0.0.1:23976"])
    (HDs : walDirsAbsent k8scompactorProgram [config.walDirOf go!"k8scompactor.etcd" go!""])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ⊢ etcdstart.premises (GF := k8scompactorGF) (hG := heapAtKc hG lctx) go!"k8scompactor"
        go!"127.0.0.1:23986" go!"127.0.0.1:23976" n id ctxs boot)
    (Hafter : ∀ hG : HeapGS .hasLC k8scompactorGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8scompactorProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_compactor_adequate Hctx Hcec id ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo HNs HAs HDs n Hprem Hafter
    σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

/-- **The compactor example on three members under partitions is safe, in the operational
semantics** (`k8s_compactor_partition_adequate`, see the file header and `Adequacy.lean`). -/
theorem k8s_compactor_partition_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextReadErrs (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextErrsClient (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8scompactorPProgram steps) k8scompactorNames)
    (HAs : addrsUnclaimed (k8scompactorPProgram steps) k8scompactorPAddrs)
    (HDsNd : k8scompactorPWalDirs.Nodup)
    (HDs : walDirsAbsent (k8scompactorPProgram steps) k8scompactorPWalDirs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ⊢ cluster3.premises (GF := k8scompactorGF) (hG := heapAtKc hG lctx) k8s_compactor.clusterCfg n
        id₁ id₂ id₃ ps ctxs boot)
    (Hafter : ∀ hG : HeapGS .hasLC k8scompactorGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8scompactorPProgram steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_compactor_partition_adequate Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo steps
    Hsteps HNs HAs HDsNd HDs n Hprem Hafter σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn

end adequacy

#print axioms k8s_compactor_Main
#print axioms k8s_compactor_adequate
#print axioms k8s_compactor_safe
#print axioms k8s_compactor_MainPartition
#print axioms k8s_compactor_partition_adequate
#print axioms k8s_compactor_partition_safe

end EtcdGrove
end Perennial
