/- Lean-first (no Rocq counterpart).

# `etcd/leaseexpiryN`: the top-level robustness result, stated

`etcd_leaseexpiryN_robust_single_process`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/TopLevelRobustness.lean`.

(2026-11-23, etcd-grove#28, `notes/single-process-restore.md`: retired at the net swap, tag
`single-process-final`, and restored over the net extension, `etcdNetExts`, under the `_single_process`
name; against the tag the statement gains the instance argument `[net.FieldAssumptions]`, and its
semantics the net extension; the network's initial state is `Robust`'s own premise.)

(2026-11-24, P6 of the pure-premises plan) `k` is a `uint64`, `Main`'s own argument, and the premises
`1 ≤ k` and `k ≤ 1000` are gone: `Main` checks them (`if k < 1 || k > 1000 { return }`; its addresses and
directories, `leaseexpiryNAddrs k` and `leaseexpiryNDirs k`, are then empty). It took a `Nat` before,
cast to `uint64` in the program; without the range premise a `Nat` at or above `2^64` would run a
cluster other than the one the premises describe.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.TopLevelDefs
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

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

variable [go_gctx : GoGlobalContext]

/-- **`etcd_leaseexpiryN_safe_single_process` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `etcd_leaseexpiryN_safe_single_process`'s other hypotheses: in every
execution of fewer than `2 ^ 48` steps along which fewer than `2 ^ 28` threads are
live, no thread is stuck and none has an unrecovered panic. -/
def etcd_leaseexpiryN_robust_single_process.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetNGF, ContextReadErrs (GF := putgetNGF) (hG := heapAtN hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetNGF, ContextErrsClient (GF := putgetNGF) (hG := heapAtN hG lctx))
    (k : w64) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hlen : ids.length = uint.nat k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Hap : leaseIdsApart ids) (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota)
    (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk) (Hlp : leasePeersOk)
    (HAs : addrsUnclaimed (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNAddrs k))
    (HDs : dataDirsAbsent (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNDirs k))
    (HEnv : verifyEnvOff (leaseexpiryNProgram k))
    (Hprem : ∀ n : Nat, ∀ hG : HeapGS .hasLC putgetNGF,
      ⊢ etcd_leaseexpiryN.premises (GF := putgetNGF) (hG := heapAtN hG lctx) (uint.nat k) n ids ps ctxs
        boot)
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcd_leaseexpiryN.leaseexpiryNDirs k)),
    Robustness.Robust [] [(leaseexpiryNProgram k, σ)] g (threads := 2 ^ 28)
      (bound := 2 ^ 48)

end adequacy
end EtcdGrove
end Perennial

end
