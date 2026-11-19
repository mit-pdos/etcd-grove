/- Lean-first (no Rocq counterpart).

# `etcd/txnlin`: the top-level robustness result, stated

`etcd_txnlin_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/txnlin/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.TopLevelDefs
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

/-- **`etcd_txnlin_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_txnlin_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_txnlin_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvtxnGF, ContextReadErrs (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC linkvtxnGF, ContextErrsClient (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (linkvtxnProgram clients ops) linkvtxnNames)
    (HAs : addrsUnclaimed (linkvtxnProgram clients ops) [go!"127.0.0.1:23796"])
    (HDs : dataDirsAbsent (linkvtxnProgram clients ops) [go!"/tmp/etcd-grove-data/linkvtxn.etcd"])
    (HEnv : verifyEnvOff (linkvtxnProgram clients ops))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC linkvtxnGF,
      ⊢ etcd_txnlin.premises (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"/tmp/etcd-grove-data/linkvtxn.etcd"]),
    Robustness.Robust [] [(linkvtxnProgram clients ops, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
