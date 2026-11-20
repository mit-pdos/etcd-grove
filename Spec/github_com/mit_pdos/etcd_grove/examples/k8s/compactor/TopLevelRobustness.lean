/- Lean-first (no Rocq counterpart).

# `k8s/compactor`: the top-level robustness results, stated

`k8s_compactor_robust`, `k8s_compactor_partition_robust`: the example's closed theorems as instances of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states them (to audit); the proofs are in
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Robustness.Statement
public import Spec.k8s_io.utils.clock.RealClock__After

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section adequacy

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

variable [go_gctx : GoGlobalContext]

/-- **`k8s_compactor_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `k8s_compactor_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def k8s_compactor_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextReadErrs (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextErrsClient (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcdstart.BootFacts id ctxs boot) (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota)
    (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed k8scompactorProgram k8scompactorNames)
    (HAs : addrsUnclaimed k8scompactorProgram [go!"127.0.0.1:23976"])
    (HDs : dataDirsAbsent k8scompactorProgram [go!"/tmp/etcd-grove-data/k8scompactor.etcd"])
    (HEnv : verifyEnvOff k8scompactorProgram)
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8scompactorGF,
      ⊢ etcdstart.premises (GF := k8scompactorGF) (hG := heapAtKc hG lctx) go!"k8scompactor"
        go!"127.0.0.1:23986" go!"127.0.0.1:23976" n id ctxs boot)
    (Hafter : ∀ hG : HeapGS .hasLC k8scompactorGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"/tmp/etcd-grove-data/k8scompactor.etcd"]),
    Robustness.Robust [] [(k8scompactorProgram, σ)] g (2 ^ 28 - 1)

/-- **`k8s_compactor_partition_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `k8s_compactor_partition_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def k8s_compactor_partition_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextReadErrs (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ContextErrsClient (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8scompactorPProgram steps) k8scompactorNames)
    (HAs : addrsUnclaimed (k8scompactorPProgram steps) k8scompactorPAddrs)
    (HDs : dataDirsAbsent (k8scompactorPProgram steps) k8scompactorPDataDirs)
    (HEnv : verifyEnvOff (k8scompactorPProgram steps))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8scompactorGF,
      ⊢ cluster3.premises (GF := k8scompactorGF) (hG := heapAtKc hG lctx) k8s_compactor.clusterCfg n
        id₁ id₂ id₃ ps ctxs boot)
    (Hafter : ∀ hG : HeapGS .hasLC k8scompactorGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) k8scompactorPDataDirs),
    Robustness.Robust [] [(k8scompactorPProgram steps, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
