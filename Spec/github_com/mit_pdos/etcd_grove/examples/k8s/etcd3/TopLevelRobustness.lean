/- Lean-first (no Rocq counterpart).

# `k8s/etcd3`: the top-level robustness results, stated

`k8s_etcd3_robust`, `k8s_etcd3_cluster_robust`, `k8s_etcd3_partition_robust`: the example's closed theorems as instances of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states them (to audit); the proofs are in
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.TopLevelDefs
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Robustness.Statement

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

/-- **`k8s_etcd3_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `k8s_etcd3_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def k8s_etcd3_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextErrsClient (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers)
    (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3Program clients ops watchers wops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3Program clients ops watchers wops) [go!"127.0.0.1:23896"])
    (HDs : dataDirsAbsent (k8setcd3Program clients ops watchers wops) [go!"/tmp/etcd-grove-data/k8setcd3.etcd"])
    (HEnv : verifyEnvOff (k8setcd3Program clients ops watchers wops))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"/tmp/etcd-grove-data/k8setcd3.etcd"]),
    Robustness.Robust [] [(k8setcd3Program clients ops watchers wops, σ)] g (2 ^ 28 - 1)

/-- **`k8s_etcd3_cluster_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `k8s_etcd3_cluster_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def k8s_etcd3_cluster_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextErrsClient (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk) (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients)
    (Hw0 : 0 ≤ sint.Z watchers) (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3CProgram k clients ops watchers wops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3CProgram k clients ops watchers wops) (k8s_etcd3N.k8setcd3NAddrs k))
    (HDs : dataDirsAbsent (k8setcd3CProgram k clients ops watchers wops) (k8s_etcd3N.k8setcd3NDirs k))
    (HEnv : verifyEnvOff (k8setcd3CProgram k clients ops watchers wops))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8s_etcd3N.k8setcd3NDirs k)),
    Robustness.Robust [] [(k8setcd3CProgram k clients ops watchers wops, σ)] g (2 ^ 28 - 1)

/-- **`k8s_etcd3_partition_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `k8s_etcd3_partition_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def k8s_etcd3_partition_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextErrsClient (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk) (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients)
    (Hw0 : 0 ≤ sint.Z watchers) (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8setcd3PProgram k clients ops watchers wops steps) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3PProgram k clients ops watchers wops steps) (k8s_etcd3N.k8setcd3NAddrs k))
    (HDs : dataDirsAbsent (k8setcd3PProgram k clients ops watchers wops steps) (k8s_etcd3N.k8setcd3NDirs k))
    (HEnv : verifyEnvOff (k8setcd3PProgram k clients ops watchers wops steps))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8s_etcd3N.k8setcd3NDirs k)),
    Robustness.Robust [] [(k8setcd3PProgram k clients ops watchers wops steps, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
