/- Lean-first (no Rocq counterpart).

# `etcd/restart`: the top-level robustness result, stated

`etcd_restart3_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/restart/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.TopLevelDefs
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

/-- **`etcd_restart3_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_restart3_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_restart3_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restart3GF, ContextReadErrs (GF := restart3GF) (hG := heapAtR3 hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_restart.BootFacts id₁ id₂ id₃ ps ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart3Program restart3Names)
    (HAs : addrsUnclaimed restart3Program restart3Addrs)
    (HDs : dataDirsAbsent restart3Program
      [(etcd_restart.name₁ ++ go!".etcd"), (etcd_restart.name₂ ++ go!".etcd"), (etcd_restart.name₃ ++ go!".etcd")])
    (HEnv : verifyEnvOff restart3Program)
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC restart3GF,
      ⊢ etcd_restart.premises (GF := restart3GF) (hG := heapAtR3 hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [(etcd_restart.name₁ ++ go!".etcd"), (etcd_restart.name₂ ++ go!".etcd"), (etcd_restart.name₃ ++ go!".etcd")]),
    Robustness.Robust [] [(restart3Program, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
