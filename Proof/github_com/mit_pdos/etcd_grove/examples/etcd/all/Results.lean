/- Lean-first (no Rocq counterpart).

# `etcd/all`: the single-process closed etcd theorem, `etcd_safe_single_process`

The program of `examples/etcd/all` runs eleven etcd examples, each on a cluster of its own, in one
process and at once, in four parts (`notes/etcd-unified-scope.md`; the statement's header,
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`): **KV** (txnlinfaultsN on
`k₁` members under the partition schedule `steps₁`, partition's watch workload on three under `steps₂`,
compactwatch, compacted and cache on one member each), **Auth** (authN on `k₂`, authlease on `k₃`),
**Lease** (leaseN on `k₄`, leasecatchup on three) and **Restart** (restartN on `k₅`, restart1 on one).
Each driver panics if its check fails.

`etcd_safe_single_process` (`etcd_safe` until the net swap, 2026-11-22, whose name the distributed theorem
took; restored 2026-11-23 over the net extension, `notes/single-process-restore.md`) is `etcd_adequate_of` (`Adequacy.lean`) applied to `Main`'s linked triple
(`MainLinked.lean`'s `etcd_all.wp_Main`, over the eleven drivers' linked `Main` results): in every real
execution of fewer than `2 ^ 48` steps along which fewer than `2 ^ 28` threads are live, from a
fresh state with one thread, no thread is stuck, none has ended in a panic, and the main thread's
result, if any, is `#()`. Its premises are `etcd_robust_single_process.spec`'s, at one `n`; `Hlow` (`_Hlow`: the 16
low bits of the ids of all the process's members distinct, the condition of idutil's trusted model) is
stated, not used. `TopLevelRobustness.lean` restates it as `etcd_robust_single_process`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.MainLinked
public import Robustness.Statement

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_all.wp_Main`). -/
theorem etcd_all_Main
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
    etcd_all.Main.spec (GF := GF) (hG := hG) :=
  etcd_all.wp_Main

end results

section adequacy
attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet
variable [go_gctx : GoGlobalContext]

/-- **The single-process closed etcd theorem** (see the file header; `etcd_safe` until the net swap,
restored 2026-11-23 over the net extension, `notes/single-process-restore.md`): the eleven examples at once in one process,
for every `1 ≤ k₁ ≤ 1000`, `1 ≤ k₂, k₃, k₄ ≤ 300`, `3 ≤ k₅ ≤ 300`, every two schedules and every
workload within the bounds: in every real execution of `n` steps (`n + 1 ≤ 2 ^ 48`) from a fresh state
with one thread and a network with no connection, along which fewer than `2 ^ 28` threads are live, no thread is stuck, none has ended
in a panic, and the main thread's result, if any, is `#()`. -/
theorem etcd_safe_single_process [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    [_root_.Perennial.net.FieldAssumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC etcdGF, ContextReadErrs (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC etcdGF, ContextErrsClient (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    -- KV: txnlinfaultsN's cluster, `k₁` members
    (k₁ : Nat) (hk₁1 : 1 ≤ k₁) (hk₁ : k₁ ≤ 1000) (ids₁ ps₁ : List w64) (ctxs₁ : List (List w8))
    (boot₁ : List LogEntry) (Hlen₁ : ids₁.length = k₁)
    (Hbf₁ : etcd_txnlinfaultsN.BootFacts ids₁ ps₁ ctxs₁ boot₁)
    -- KV: partition's cluster (three members)
    (pid₁ pid₂ pid₃ : w64) (psP : List w64) (ctxsP : List (List w8)) (bootP : List LogEntry)
    (HbfP : etcd_partition.BootFacts pid₁ pid₂ pid₃ psP ctxsP bootP)
    -- KV: compactwatch's, compacted's and cache's one-member clusters
    (cwId : w64) (ctxsCW : List (List w8)) (bootCW : List LogEntry)
    (HbfCW : etcd_compactwatch.BootFacts cwId ctxsCW bootCW)
    (cId : w64) (ctxsC : List (List w8)) (bootC : List LogEntry)
    (HbfC : etcd_compacted.BootFacts cId ctxsC bootC)
    (kvId : w64) (ctxsK : List (List w8)) (bootK : List LogEntry)
    (HbfK : etcd_putget.BootFacts kvId ctxsK bootK)
    -- Auth: authN's cluster, `k₂` members, and authlease's, `k₃` (their ids apart in 15 bits)
    (k₂ : Nat) (hk₂1 : 1 ≤ k₂) (hk₂ : k₂ ≤ 300) (ids₂ ps₂ : List w64) (ctxs₂ : List (List w8))
    (boot₂ : List LogEntry) (Hlen₂ : ids₂.length = k₂)
    (Hbf₂ : etcd_putgetN.BootFacts ids₂ ps₂ ctxs₂ boot₂)
    (k₃ : Nat) (hk₃1 : 1 ≤ k₃) (hk₃ : k₃ ≤ 300) (ids₃ ps₃ : List w64) (ctxs₃ : List (List w8))
    (boot₃ : List LogEntry) (Hlen₃ : ids₃.length = k₃)
    (Hbf₃ : etcd_putgetN.BootFacts ids₃ ps₃ ctxs₃ boot₃) (Hap : leaseIdsApart ids₃)
    -- Lease: leaseN's cluster, `k₄` members, and leasecatchup's (three members)
    (k₄ : Nat) (hk₄1 : 1 ≤ k₄) (hk₄ : k₄ ≤ 300) (ids₄ ps₄ : List w64) (ctxs₄ : List (List w8))
    (boot₄ : List LogEntry) (Hlen₄ : ids₄.length = k₄)
    (Hbf₄ : etcd_putgetN.BootFacts ids₄ ps₄ ctxs₄ boot₄)
    (lid₁ lid₂ lid₃ : w64) (psL : List w64) (ctxsL : List (List w8)) (bootL : List LogEntry)
    (HbfL : cluster3.BootFacts lid₁ lid₂ lid₃ psL ctxsL bootL)
    -- Restart: restartN's cluster, `k₅` members, and restart1's one member
    (k₅ : Nat) (hk₅3 : 3 ≤ k₅) (hk₅ : k₅ ≤ 300) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8))
    (boot₅ : List LogEntry) (Hlen₅ : ids₅.length = k₅)
    (Hbf₅ : etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (HbfR : etcd_restart1.BootFacts rId ctxsR bootR)
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (_Hlow : ((ids₁ ++ [pid₁, pid₂, pid₃, cwId, cId, kvId] ++ ids₂ ++ ids₃ ++ ids₄ ++
      [lid₁, lid₂, lid₃] ++ ids₅ ++ [rId]).map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    -- the server's workload and environment
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- peers answer `/leases/internal` as etcd's handler does or not with 200; no lease expires in the run
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    -- txnlinfaultsN's workload and schedule
    (clients ops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps₁ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps₁ : steps₁.length < 2 ^ 63)
    -- partition's watch workload and schedule
    (nw nops : w64) (Hnw0 : 0 ≤ sint.Z nw) (Hnw31 : sint.Z nw < 2 ^ 31) (Hnops : 0 ≤ sint.Z nops)
    (Hnmul : sint.Z nw * sint.Z nops < 2 ^ 62)
    (steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps₂ : steps₂.length < 2 ^ 63)
    -- cache's workload
    (cnw cnops : w64) (Hcnw0 : 0 ≤ sint.Z cnw) (Hcnw31 : sint.Z cnw < 2 ^ 31)
    (Hcnops : 0 ≤ sint.Z cnops) (Hcmul : sint.Z cnw * sint.Z cnops < 2 ^ 62)
    -- the program's addresses, data directories and environment
    (HAs : addrsUnclaimed (etcdProgram k₁ clients ops steps₁ nw nops steps₂ cnw cnops k₂ k₃ k₄ k₅)
      (etcdAddrs k₁ k₂ k₃ k₄ k₅))
    (HDs : dataDirsAbsent (etcdProgram k₁ clients ops steps₁ nw nops steps₂ cnw cnops k₂ k₃ k₄ k₅)
      (etcdDirs k₁ k₂ k₃ k₄ k₅))
    (HEnv : verifyEnvOff (etcdProgram k₁ clients ops steps₁ nw nops steps₂ cnw cnops k₂ k₃ k₄ k₅))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_txnlinfaultsN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) k₁ n ids₁ ps₁ ctxs₁ boot₁)
    (HpremP : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_partition.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n pid₁ pid₂ pid₃ psP ctxsP
          bootP)
    (HpremCW : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_compactwatch.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n cwId ctxsCW bootCW)
    (HpremC : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_compacted.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n cId ctxsC bootC)
    (HpremK : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_cache.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n kvId ctxsK bootK)
    (Hprem₂ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_authN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) k₂ n ids₂ ps₂ ctxs₂ boot₂)
    (Hprem₃ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_authlease.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) k₃ n ids₃ ps₃ ctxs₃ boot₃)
    (Hprem₄ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_leaseN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) k₄ n ids₄ ps₄ ctxs₄ boot₄)
    (HpremL : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ cluster3.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) etcd_leasecatchup.clusterCfg n
          lid₁ lid₂ lid₃ psL ctxsL bootL)
    (Hprem₅ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restartN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) k₅ n ids₅ ps₅ ctxs₅ boot₅)
    (HpremR : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restart1.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n rId ctxsR bootR)
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcdDirs k₁ k₂ k₃ k₄ k₅))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n
      ([etcdProgram k₁ clients ops steps₁ nw nops steps₂ cnw cnops k₂ k₃ k₄ k₅], ((σ, g) : CfgState))
      κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_adequate_of (fun hG => etcd_all.wp_Main (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    Hctx Hcec k₁ hk₁1 hk₁ ids₁ ps₁ ctxs₁ boot₁ Hlen₁ Hbf₁ pid₁ pid₂ pid₃ psP ctxsP bootP HbfP cwId
    ctxsCW bootCW HbfCW cId ctxsC bootC HbfC kvId ctxsK bootK HbfK k₂ hk₂1 hk₂ ids₂ ps₂ ctxs₂ boot₂
    Hlen₂ Hbf₂ k₃ hk₃1 hk₃ ids₃ ps₃ ctxs₃ boot₃ Hlen₃ Hbf₃ Hap k₄ hk₄1 hk₄ ids₄ ps₄ ctxs₄ boot₄
    Hlen₄ Hbf₄ lid₁ lid₂ lid₃ psL ctxsL bootL HbfL k₅ hk₅3 hk₅ ids₅ ps₅ ctxs₅ boot₅ Hlen₅ Hbf₅ rId
    ctxsR bootR HbfR Haf Hbuq Hrf Hdbo Hlp Hlne clients ops Hc0 Hc31 Hops Hmul steps₁ Hsteps₁ nw
    nops Hnw0 Hnw31 Hnops Hnmul steps₂ Hsteps₂ cnw cnops Hcnw0 Hcnw31 Hcnops Hcmul HAs HDs HEnv
    n Hprem₁ HpremP HpremCW HpremC HpremK Hprem₂ Hprem₃ Hprem₄ HpremL Hprem₅ HpremR σ g Hg Hfs HWal
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn

end adequacy

#print axioms etcd_all_Main
#print axioms etcd_adequate_of
#print axioms etcd_safe_single_process

end EtcdGrove
end Perennial
