/- Lean-first (no Rocq counterpart).

# `etcd/watch`: the top-level robustness result, stated

`etcd_watch_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/watch/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.TopLevelDefs
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

/-- **`etcd_watch_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_watch_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def etcd_watch_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.watch.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk) (nw nops : w64)
    (H0 : 0 ≤ sint.Z nw) (H31 : sint.Z nw < 2 ^ 31) (Hops : 0 ≤ sint.Z nops)
    (Hmul : sint.Z nw * sint.Z nops < 2 ^ 62)
    (HNs : prometheus.namesUnclaimed (watchkvProgram nw nops) watchkvNames)
    (HAs : addrsUnclaimed (watchkvProgram nw nops) [go!"127.0.0.1:23872"])
    (HDs : dataDirsAbsent (watchkvProgram nw nops) [go!"/tmp/etcd-grove-data/watchkv.etcd"])
    (HEnv : verifyEnvOff (watchkvProgram nw nops))
    (Hprem : ∀ n : Nat, n + 2 ≤ 2 ^ 28 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_watch.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"/tmp/etcd-grove-data/watchkv.etcd"]),
    Robustness.Robust [] [(watchkvProgram nw nops, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end
