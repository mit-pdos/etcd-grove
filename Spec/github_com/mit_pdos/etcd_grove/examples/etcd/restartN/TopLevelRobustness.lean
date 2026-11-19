/- Lean-first (no Rocq counterpart).

# `etcd/restartN`: the top-level robustness result, stated

`etcd_restartN_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.TopLevelDefs
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

/-- **`etcd_restartN_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_restartN_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_restartN_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restartNGF, ContextReadErrs (GF := restartNGF) (hG := heapAtRN hG lctx))
    (k : Nat) (hk3 : 3 ≤ k) (hk : k ≤ 1000) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = k) (Hbf : etcd_restartN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (restartNProgram k) restartNNames)
    (HAs : addrsUnclaimed (restartNProgram k) (etcd_restartN.restartNAddrs k))
    (HDs : dataDirsAbsent (restartNProgram k) (etcd_restartN.restartNDirs k))
    (HEnv : verifyEnvOff (restartNProgram k))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC restartNGF,
      ⊢ etcd_restartN.premises (GF := restartNGF) (hG := heapAtRN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcd_restartN.restartNDirs k)),
    Robustness.Robust [] [(restartNProgram k, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
