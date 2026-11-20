/-
**The one closed Kubernetes theorem's results** (`examples/k8s/all`; `notes/k8s-unified-scope.md`, the
user's decisions of 2026-11-20), restated, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8s_all_Main`** (`MainLinked.lean`'s `k8s_all.wp_Main`): `Main(k, clients, ops, watchers, wops,
  sched1, sched2)` does not panic: the two drivers' `MainPartition` triples side by side
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/Main.lean`), under the named hypothesis of
  `clock.RealClock.After`.
* **`k8s_safe`** (`Adequacy.lean`'s `k8s_adequate`): the closed theorem. Every real execution of `n`
  steps of the package's initialization followed by `Main` with the two schedules built as slice
  literals, from a fresh state with one thread, for every `1 ≤ k ≤ 1000` and every two schedules: no
  thread is stuck, no thread has ended in a panic (the store driver's porcupine check of its history
  against its model, each API server's check of its compactor), and the main thread's result, if any,
  is `#()`. Its premises are the union of the two retired partition theorems'
  (`k8s_etcd3_partition_safe`, `k8s_compactor_partition_safe`) and `Hlow`: the 16 low bits of the ids
  of the process's every member (both clusters') are distinct, the precondition of the trusted model of
  etcd's request-id generator (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`), checked by
  `examples/k8s/all`'s `TestMemberIDs`. The proof does not use `Hlow`: it states the condition under
  which that trusted model is faithful of this program.

These replace the two drivers' five closed theorems (`k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`,
`k8s_etcd3_partition_safe`, `k8s_compactor_safe`, `k8s_compactor_partition_safe`), retired on
2026-11-20 (the user's decision D3); the drivers' function triples stay in their `Results.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Adequacy
public import Robustness.Statement

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`MainLinked.lean`'s `k8s_all.wp_Main`). -/
theorem k8s_all_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)]
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_all.Main.spec (GF := GF) (hG := hG) :=
  k8s_all.wp_Main h_After

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs
variable [go_gctx : GoGlobalContext]

/-- **The one closed Kubernetes theorem** (`k8s_adequate`, see the file header and `Adequacy.lean`):
the Kubernetes etcd3 store's partitioned workload on `k` members and Kubernetes' compactor under
partitions on three more members, at once in one process, for every `1 ≤ k ≤ 1000` and every two
schedules: in every real execution of `n` steps from a fresh state with one thread, no thread is
stuck, none has ended in a panic, and the main thread's result, if any, is `#()`. -/
theorem k8s_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8sGF, ContextReadErrs (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8sGF, ContextErrsClient (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    -- the store's cluster: `k` members
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    -- the compactor's cluster: three members
    (id₁ id₂ id₃ : w64) (ps' : List w64) (ctxs' : List (List w8)) (boot' : List LogEntry)
    (Hbf' : cluster3.BootFacts id₁ id₂ id₃ ps' ctxs' boot')
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (_Hlow : ((ids ++ [id₁, id₂, id₃]).map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the store's workload
    (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers)
    (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    -- the two partition schedules
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps₁ : steps₁.length < 2 ^ 63) (Hsteps₂ : steps₂.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8sProgram k clients ops watchers wops steps₁ steps₂) k8sNames)
    (HAs : addrsUnclaimed (k8sProgram k clients ops watchers wops steps₁ steps₂) (k8sAddrs k))
    (HDs : dataDirsAbsent (k8sProgram k clients ops watchers wops steps₁ steps₂) (k8sDirs k))
    (HEnv : verifyEnvOff (k8sProgram k clients ops watchers wops steps₁ steps₂))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k n ids ps ctxs boot)
    (Hprem₂ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ cluster3.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k8s_compactor.clusterCfg n
        id₁ id₂ id₃ ps' ctxs' boot')
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sDirs k))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8sProgram k clients ops watchers wops steps₁ steps₂],
      ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  k8s_adequate Hctx Hcec Hafter k hk1 hk ids ps ctxs boot Hlen Hbf id₁ id₂ id₃ ps' ctxs' boot' Hbf'
    Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0 Hw0 Hc31 Hops Hwops Hmul steps₁ steps₂ Hsteps₁
    Hsteps₂ HNs HAs HDs HEnv n Hprem₁ Hprem₂ σ g Hfs HWal Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn

end adequacy

#print axioms k8s_all_Main
#print axioms k8s_adequate
#print axioms k8s_safe

end EtcdGrove
end Perennial
