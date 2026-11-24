/- Lean-first (no Rocq counterpart).

# `k8s/all`: the one closed Kubernetes theorem, stated

`k8s_robust_single_process`: the closed theorem of `examples/k8s/all` (`notes/k8s-unified-scope.md`, the user's
decisions of 2026-11-20) as an instance of the generic robustness statement (`Robustness/Statement.lean`,
`Robust crashing stable g threads bound`: in every execution of the machines that may crash and restart and of
those that never crash, each a fresh Go process, of fewer than `bound` steps, no thread is stuck and
none has an unrecovered panic). The program runs, in one process and at once, the Kubernetes etcd3
store's workload on `k₁` etcd members under the partition schedule `steps₁` (porcupine checks the
history against the driver's model of the store, and the driver panics if it is not linearizable) and
Kubernetes' compactor run by five API servers and a writer on `k₂` more members under the schedule
`steps₂` (each API server panics if its compactor's revision decreases or runs ahead of the cluster):
so no such check fails, for every `1 ≤ k₁ ≤ 1000`, every `1 ≤ k₂ ≤ 600` and every two schedules. It
replaces the two drivers' five separate theorems (retired 2026-11-20); the compactor's cluster has `k₂`
members since 2026-11-20 (`notes/k8s-compactor-n-plan.md`, approved by the user), three before. This file only states it (to audit); the proof
is in `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/all/TopLevelRobustness.lean`.

**The premises** are the union of the two drivers' theorems' (`k8s_etcd3_partition_safe`'s and
`k8s_compactor_partition_safe`'s, now retired): each cluster's member ids and bootstrap log
(`BootFacts`), the server's four opaque workload and environment premises once, the store workload's
bounds, the schedules' lengths, the program's addresses and data directories (both
clusters', concatenated), `ETCD_VERIFY` off, each cluster's named premises (`Hprem₁`, `Hprem₂`, at one
step bound), `time.After`'s contract (the compactor's), the file system's initial state and the members'
WAL areas; and one new premise, `Hlow`: the 16 low bits of the ids of the process's every member
(both clusters') are distinct, the precondition of the trusted model of etcd's request-id generator
(`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`: no two generators of the process issue one id),
checked for every `k₁ ≤ 1000` and `k₂ ≤ 600` by `examples/k8s/all`'s `TestMemberIDs` (the bound on
`k₂`: with the store's 1000 ids fixed, no compactor token keeps 1000 more distinct; the plan's §3).
The proof does not use it: it
states the condition under which that trusted model is faithful (each cluster's own `BootFacts` states
it for that cluster, `BootCore.lowNodup`).

(2026-11-23, etcd-grove#28, `notes/single-process-restore.md`: retired at the net swap, tag
`single-process-final`, and restored over the net extension, `etcdNetExts`, under the `_single_process`
name; against the tag the statement gains the instance argument `[net.FieldAssumptions]`, and its
semantics the net extension; the network's initial state is `Robust`'s own premise.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainDefs
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Robustness.Statement
public import Spec.k8s_io.utils.clock.RealClock__After

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

/-- **`k8s_safe_single_process` as a robustness statement** (`Robustness.Robust`, `Robustness/Statement.lean`; see
the file header): the program alone on one machine that never crashes, a fresh Go process (`Robust`'s
premise), under `k8s_safe_single_process`'s other hypotheses (its boot premises `Hprem₁`/`Hprem₂` at every `n` with
`n + 1 ≤ 2 ^ 48`, as `etcd_robust`'s): in every execution of fewer than `2 ^ 48` steps along
which fewer than `2 ^ 28` threads are live, no thread is stuck and none has an unrecovered panic. -/
def k8s_robust_single_process.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    -- (wal-nostorageok, 2026-11-21: for the premise `rnNewStorageOk`) `os`'s field steps
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC k8sGF, ContextReadErrs (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8sGF, ContextErrsClient (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    -- the store's cluster: `k₁` members
    (k₁ : Nat) (hk₁1 : 1 ≤ k₁) (hk₁ : k₁ ≤ 1000) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    -- the compactor's cluster: `k₂` members
    (k₂ : Nat) (hk₂1 : 1 ≤ k₂) (hk₂ : k₂ ≤ 600) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (Hlow : ((ids ++ ids').map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the store's workload
    (clients ops watchers wops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers)
    (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)
    -- the two partition schedules
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps₁ : steps₁.length < 2 ^ 63) (Hsteps₂ : steps₂.length < 2 ^ 63)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂) (k8sDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂))
    (Hprem₁ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₁ n ids ps ctxs boot)
    (Hprem₂ : ∀ n : Nat, n + 1 ≤ 2 ^ 48 → ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) k₂ n ids' ps' ctxs' boot')
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sDirs k₁ k₂)),
    Robustness.Robust [] [(k8sProgram k₁ clients ops watchers wops steps₁ k₂ steps₂, σ)] g
      (threads := 2 ^ 28) (bound := 2 ^ 48)

end adequacy
end EtcdGrove
end Perennial

end
