/- Lean-first (no Rocq counterpart).

# `etcd/partition`: the top-level robustness results, stated

`etcd_partition_robust`, `etcd_partition_watch_robust`: the example's closed theorems as instances of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states them (to audit); the proofs are in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/partition/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.TopLevelDefs
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

/-- **`etcd_partition_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_partition_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 40 - 11` steps along which fewer than `2 ^ 28` threads are
live, no thread is stuck and none has an unrecovered panic. -/
def etcd_partition_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC linkvGF, ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_partition.BootFacts id₁ id₂ id₃ ps ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (linkv3pProgram clients ops steps) linkv3pNames)
    (HAs : addrsUnclaimed (linkv3pProgram clients ops steps) linkv3pAddrs)
    (HDs : dataDirsAbsent (linkv3pProgram clients ops steps) [(memberDataDir etcd_partition.name₁), (memberDataDir etcd_partition.name₂), (memberDataDir etcd_partition.name₃)])
    (HEnv : verifyEnvOff (linkv3pProgram clients ops steps))
    (Hprem : ∀ n : Nat, ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ etcd_partition.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [(memberDataDir etcd_partition.name₁), (memberDataDir etcd_partition.name₂), (memberDataDir etcd_partition.name₃)]),
    Robustness.Robust [] [(linkv3pProgram clients ops steps, σ)] g (threads := 2 ^ 28)
      (bound := 2 ^ 40 - 11)

/-- **`etcd_partition_watch_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_partition_watch_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 40 - 11` steps along which fewer than `2 ^ 28` threads are
live, no thread is stuck and none has an unrecovered panic. -/
def etcd_partition_watch_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC linkvGF,
      ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_partition.BootFacts id₁ id₂ id₃ ps ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk) (nw nops : w64)
    (H0 : 0 ≤ sint.Z nw) (H31 : sint.Z nw < 2 ^ 31) (Hops : 0 ≤ sint.Z nops)
    (Hmul : sint.Z nw * sint.Z nops < 2 ^ 62)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (linkv3pWatchProgram nw nops steps) linkv3pNames)
    (HAs : addrsUnclaimed (linkv3pWatchProgram nw nops steps) linkv3pAddrs)
    (HDs : dataDirsAbsent (linkv3pWatchProgram nw nops steps) [(memberDataDir etcd_partition.name₁), (memberDataDir etcd_partition.name₂), (memberDataDir etcd_partition.name₃)])
    (HEnv : verifyEnvOff (linkv3pWatchProgram nw nops steps))
    (Hprem : ∀ n : Nat, ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ etcd_partition.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [(memberDataDir etcd_partition.name₁), (memberDataDir etcd_partition.name₂), (memberDataDir etcd_partition.name₃)]),
    Robustness.Robust [] [(linkv3pWatchProgram nw nops steps, σ)] g (threads := 2 ^ 28)
      (bound := 2 ^ 40 - 11)

end adequacy
end EtcdGrove
end Perennial

end
