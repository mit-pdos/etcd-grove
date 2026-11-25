/-
**The one closed Kubernetes theorem's results** (`examples/k8s/all`; `notes/k8s-unified-scope.md`, the
user's decisions of 2026-11-20), restated, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8s_all_Main`** (`MainLinked.lean`'s `k8s_all.wp_Main`): `Main(k1, clients, ops, watchers, wops,
  sched1, k2, sched2)` does not panic: the two drivers' `MainPartition` triples side by side
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/Main.lean`), under the named hypothesis of
  `clock.RealClock.After`; **`k8s_all_MainChecked`**, the program's entry point, likewise.
* **`k8s_safe_single_process`** (`Adequacy.lean`'s `k8s_adequate`): the closed theorem. Every real execution of `n`
  steps of the package's initialization followed by `MainChecked` (the pure-premises plan's P5,
  2026-11-24: `Main` behind `ParamsOk`, with schedules it draws), from a fresh state with one thread,
  for all member counts, workloads and schedule lengths (`MainChecked` runs `Main` for `1 ≤ k₁ ≤ 1000`
  store members, `1 ≤ k₂ ≤ 600` compactor members, `notes/k8s-compactor-n-plan.md`, and a workload in
  its bounds, and otherwise returns): no
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

(2026-11-23, etcd-grove#28, `notes/single-process-restore.md`: retired at the net swap, tag
`single-process-final`, and restored over the net extension, `etcdNetExts`, under the `_single_process`
name; against the tag the statement gains the instance argument `[net.FieldAssumptions]` and the
network's initial state `Hg : extsInitGlobal g`, the semantics the net extension.)
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

/-- **`MainChecked`, the program's entry point, does not panic** (`MainLinked.lean`'s
`k8s_all.wp_MainChecked`). -/
theorem k8s_all_MainChecked [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_all.MainChecked.spec (GF := GF) (hG := hG) :=
  k8s_all.wp_MainChecked h_After

/-- **`Main` does not panic** (`MainLinked.lean`'s `k8s_all.wp_Main`). -/
theorem k8s_all_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG)) :
    k8s_all.Main.spec (GF := GF) (hG := hG) :=
  k8s_all.wp_Main h_After

end results

section adequacy
attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet
variable [go_gctx : GoGlobalContext]

/-- **The one closed Kubernetes theorem** (`k8s_adequate`, see the file header and `Adequacy.lean`):
the Kubernetes etcd3 store's partitioned workload on `k₁` members and Kubernetes' compactor under
partitions on `k₂` more members, at once in one process, for all member counts, workloads and schedule
lengths (`MainChecked` runs them when `1 ≤ k₁ ≤ 1000`, `1 ≤ k₂ ≤ 600` and the workload is within its
bounds, with schedules it draws, and otherwise returns): in every real execution of `n` steps from a fresh state with one thread, no thread is
stuck, none has ended in a panic, and the main thread's result, if any, is `#()`. -/
theorem k8s_safe_single_process [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    -- the store's cluster: `k₁` members
    (k₁ : w64) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = uint.nat k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    -- the compactor's cluster: `k₂` members
    (k₂ : w64) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = uint.nat k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (_Hlow : ((ids ++ ids').map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the store's workload and the two schedules' lengths (any values: `MainChecked` checks them)
    (clients ops watchers wops n₁ n₂ : w64)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂)
      (k8sProgAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂)
      (k8sProgDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) (uint.nat k₁) n ids ps ctxs boot)
    (Hprem₂ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) (uint.nat k₂) n ids' ps'
          ctxs' boot')
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sProgDirs k₁ k₂))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂],
      ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  k8s_adequate Hafter k₁ ids ps ctxs boot Hlen Hbf k₂ ids' ps' ctxs' boot' Hlen' Hbf'
    Haf Hbuq Hrf Hdbo clients ops watchers wops n₁ n₂ HAs HDs HEnv n Hprem₁ Hprem₂ σ g Hg Hfs HWal
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn

end adequacy

#print axioms k8s_all_Main
#print axioms k8s_all_MainChecked
#print axioms k8s_adequate
#print axioms k8s_adequate_below
#print axioms k8s_safe_single_process

end EtcdGrove
end Perennial
