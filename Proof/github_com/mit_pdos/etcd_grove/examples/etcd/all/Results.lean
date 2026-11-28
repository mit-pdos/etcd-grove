/- Lean-first (no Rocq counterpart).

# `etcd/all`: the single-process closed etcd theorem, `etcd_restart_safe_single_process`

The program of `examples/etcd/all` runs the restart part in one process (the statement's header,
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`): restartN on `k₅`
members and restart1 on one, at once, each on a cluster of its own. Each driver panics if its check
fails. (Until 2026-11-27 the program also ran the KV, Auth and Lease parts, nine more drivers.)

`etcd_restart_safe_single_process` (`etcd_safe` until the net swap, 2026-11-22, whose name the distributed theorem
took; restored 2026-11-23 over the net extension, `notes/single-process-restore.md`) is `etcd_adequate_of` (`Adequacy.lean`) applied to `MainChecked`'s linked triple
(`MainLinked.lean`'s `etcd_all.wp_MainChecked`, over `Main`'s, itself over the two drivers' linked
`Main` results): in every real
execution of fewer than `2 ^ 48` steps along which fewer than `2 ^ 28` threads are live, from a
fresh state with one thread, no thread is stuck, none has ended in a panic, and the main thread's
result, if any, is `#()`. Its premises are `etcd_restart_robust_single_process.spec`'s, at one `n`; `Hlow` (`_Hlow`: the 16
low bits of the ids of all the process's members distinct, the condition of idutil's trusted model) is
stated, not used. `TopLevelRobustness.lean` restates it as `etcd_restart_robust_single_process`.
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
theorem etcd_all_Main :
    etcd_all.Main.spec (GF := GF) (hG := hG) :=
  etcd_all.wp_Main

/-- **`MainChecked`, the program's entry point, does not panic** (`MainLinked.lean`'s
`etcd_all.wp_MainChecked`). -/
theorem etcd_all_MainChecked :
    etcd_all.MainChecked.spec (GF := GF) (hG := hG) :=
  etcd_all.wp_MainChecked

end results

section adequacy
attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet
variable [go_gctx : GoGlobalContext]

/-- **The single-process closed etcd theorem** (see the file header; `etcd_safe` until the net swap,
restored 2026-11-23 over the net extension, `notes/single-process-restore.md`): the restart part in one
process, for every member count (`MainChecked` runs it when `3 ≤ k₅ ≤ 300` and otherwise returns): in
every real execution of `n` steps (`n + 1 ≤ 2 ^ 48`) from a fresh state with one thread and a network
with no connection, along which fewer than `2 ^ 28` threads are live, no thread is stuck, none has ended
in a panic, and the main thread's result, if any, is `#()`. -/
theorem etcd_restart_safe_single_process [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
    [log.NewModel]
    -- restartN's cluster, `k₅` members, and restart1's one member
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8))
    (boot₅ : List LogEntry) (Hlen₅ : ids₅.length = uint.nat k₅)
    (Hbf₅ : etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (HbfR : etcd_restart1.BootFacts rId ctxsR bootR)
    -- `bootstrap`'s values Go's
    (Hbg₅ : etcd_restartN.BootGoN (uint.nat k₅) ids₅ ps₅ ctxs₅)
    (HbgR : etcd_restart1.BootGo rId ctxsR bootR)
    -- the process's every member: their ids' 16 low bits distinct (idutil's trusted model)
    (_Hlow : ((ids₅ ++ [rId]).map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    -- the server's workload and environment
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    -- the program's addresses, data directories and environment
    (HAs : addrsUnclaimed (etcdProgram k₅) (etcdProgAddrs k₅))
    (HDs : dataDirsAbsent (etcdProgram k₅) (etcdProgDirs k₅))
    (HEnv : EtcdVerifyOff) (Hfips : crypto.fips140.GodebugFips140Off)
    (n : Nat)
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcdProgDirs k₅))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n ([etcdProgram k₅], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_adequate_of (fun hG => etcd_all.wp_MainChecked (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    k₅ ids₅ ps₅ ctxs₅ boot₅ Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hbg₅ HbgR Haf Hbuq Hdbo HAs HDs HEnv Hfips
    n σ g Hg Hfs HWal Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn

end adequacy

#print axioms etcd_all_Main
#print axioms etcd_all_MainChecked
#print axioms etcd_adequate_of
#print axioms etcd_restart_safe_single_process

end EtcdGrove
end Perennial
