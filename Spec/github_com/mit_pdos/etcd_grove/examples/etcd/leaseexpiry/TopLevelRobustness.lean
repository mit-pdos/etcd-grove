/- Lean-first (no Rocq counterpart).

# `etcd/leaseexpiry`: the top-level robustness result, stated

`etcd_leaseexpiry_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiry/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.TopLevelDefs
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

/-- **`etcd_leaseexpiry_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_leaseexpiry_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 40 - 11` steps along which fewer than `2 ^ 28` threads are
live, no thread is stuck and none has an unrecovered panic. -/
def etcd_leaseexpiry_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC leaseexpiryGF, ContextReadErrs (GF := leaseexpiryGF) (hG := heapAtLex hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC leaseexpiryGF, ContextErrsClient (GF := leaseexpiryGF) (hG := heapAtLex hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_leaseexpiry.BootFacts id ctxs boot) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk) (HNs : prometheus.namesUnclaimed leaseexpiryProgram leaseexpiryNames)
    (HAs : addrsUnclaimed leaseexpiryProgram [go!"127.0.0.1:23976"])
    (HDs : dataDirsAbsent leaseexpiryProgram [go!"/tmp/etcd-grove-data/leaseexpiry.etcd"])
    (HEnv : verifyEnvOff leaseexpiryProgram)
    (Hprem : ∀ n : Nat, ∀ hG : HeapGS .hasLC leaseexpiryGF,
      ⊢ etcd_leaseexpiry.premises (GF := leaseexpiryGF) (hG := heapAtLex hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"/tmp/etcd-grove-data/leaseexpiry.etcd"]),
    Robustness.Robust [] [(leaseexpiryProgram, σ)] g (threads := 2 ^ 28)
      (bound := 2 ^ 40 - 11)

end adequacy
end EtcdGrove
end Perennial

end
