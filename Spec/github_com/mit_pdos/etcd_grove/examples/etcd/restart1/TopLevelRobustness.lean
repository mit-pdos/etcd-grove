/- Lean-first (no Rocq counterpart).

# `etcd/restart1`: the top-level robustness result, stated

`etcd_restart1_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.TopLevelDefs
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

/-- **`etcd_restart1_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_restart1_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_restart1_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restart1GF, ContextReadErrs (GF := restart1GF) (hG := heapAtR1 hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_restart1.BootFacts id ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart1Program restart1Names)
    (HDs : dataDirsAbsent restart1Program [go!"restart1.etcd"])
    (HEnv : verifyEnvOff restart1Program)
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC restart1GF,
      ⊢ etcd_restart1.premises (GF := restart1GF) (hG := heapAtR1 hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"restart1.etcd"]),
    Robustness.Robust [] [(restart1Program, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
