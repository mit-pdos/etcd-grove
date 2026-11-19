/- Lean-first (no Rocq counterpart).

# `etcd/putget3`: the top-level robustness result, stated

`etcd_putget3_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/putget3/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.TopLevelDefs
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
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

/-- **`etcd_putget3_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_putget3_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_putget3_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putget3GF, ContextReadErrs (GF := putget3GF) (hG := heapAt3 hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putget3GF, ContextErrsClient (GF := putget3GF) (hG := heapAt3 hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed putget3Program putget3Names)
    (HAs : addrsUnclaimed putget3Program putget3Addrs)
    (HDs : dataDirsAbsent putget3Program [(memberDataDir etcd_putget3.name₁), (memberDataDir etcd_putget3.name₂), (memberDataDir etcd_putget3.name₃)])
    (HEnv : verifyEnvOff putget3Program)
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC putget3GF,
      ⊢ etcd_putget3.premises (GF := putget3GF) (hG := heapAt3 hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [(memberDataDir etcd_putget3.name₁), (memberDataDir etcd_putget3.name₂), (memberDataDir etcd_putget3.name₃)]),
    Robustness.Robust [] [(putget3Program, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
