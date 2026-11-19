/- Lean-first (no Rocq counterpart).

# `etcd/txnlinfaultsN`: the top-level robustness result, stated

`etcd_txnlinfaultsN_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.TopLevelDefs
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
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

/-- **`etcd_txnlinfaultsN_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_txnlinfaultsN_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_txnlinfaultsN_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC linkvGF, ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = k)
    (Hbf : etcd_txnlinfaultsN.BootFacts ids ps ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (txnlinfaultsNProgram k clients ops steps) txnlinfaultsNNames)
    (HAs : addrsUnclaimed (txnlinfaultsNProgram k clients ops steps)
      (etcd_txnlinfaultsN.txnlinfaultsNAddrs k))
    (HDs : dataDirsAbsent (txnlinfaultsNProgram k clients ops steps)
      (etcd_txnlinfaultsN.txnlinfaultsNDirs k))
    (HEnv : verifyEnvOff (txnlinfaultsNProgram k clients ops steps))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ etcd_txnlinfaultsN.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)),
    Robustness.Robust [] [(txnlinfaultsNProgram k clients ops steps, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
