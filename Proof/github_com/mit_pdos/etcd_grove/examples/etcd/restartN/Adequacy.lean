/- Lean-first (no Rocq counterpart).

# restartN's closed theorem (`notes/restartN-plan.md`, 2026-11-15)

restart3's closed theorem (`restart/Adequacy.lean`) for `examples/etcd/restartN` at `k` members:
`etcd_adequate_members` with the `k` members' start bundles (each data directory, each peer address; no
client address is served: `restartNAddrs`, distinct loopback literals for `k ≤ 1000`), the read package's
two metric names, the trivial extension and the ghost-state bundle `restartNGF` (restart3's), from
`restartN`'s `wp_initialize'` (over the program's package table `PkgTable.lean`) and
`etcd_restartN.wp_Main` (`MainLinked.lean`). The statement, its hypotheses and what it does not say:
`Results.lean`'s `etcd_restartN_safe`.

**Over Linux files** (2026-11-16, the user's decision (A) on `wal-lean`, applied on the merge of `lean`):
the program's extensions are `[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`: the file extension's own
semantics, no premise on the environment), since `fileutil`'s package initializer, which the server's
initialization runs, probes `F_OFD_GETLK` through `syscall.FcntlFlock` over the file extension; the
theorem's one new premise is the file extension's initial state, `Fs.FsInit` (`Hfs`: the files as on
disk, the roots well formed), so it says that the program runs on a real file system. Until then the
extensions were `TrivialExt.lean`'s `[idIssueExt]`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Dir
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.TopLevelDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0. -/
def restartNGF_allG : AllG restartNGF := ⟨⟨0, rfl⟩⟩

instance restartNGF_gooseGpreS : GooseGpreS restartNGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨restartNGF_allG⟩, ⟨restartNGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := restartNGF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **The `k`-member restart example is safe** (`Results.lean`'s `etcd_restartN_safe`, with its
docstring): for every member count `3 ≤ k ≤ 1000`, every real execution of `restartNProgram k` from a
fresh state with one thread, of `n` steps: if the main thread has finished, its result is `#()`; no
thread is stuck; no thread has ended in a panic. -/
theorem etcd_restartN_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restartNGF, ContextReadErrs (GF := restartNGF) (hG := heapAtRN hG lctx))
    (k : Nat) (hk3 : 3 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_restartN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (restartNProgram k) restartNNames)
    (HAs : addrsUnclaimed (restartNProgram k) (etcd_restartN.restartNAddrs k))
    (HDs : dataDirsAbsent (restartNProgram k) (etcd_restartN.restartNDirs k))
    (HEnv : verifyEnvOff (restartNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC restartNGF,
      ⊢ etcd_restartN.premises (GF := restartNGF) (hG := heapAtRN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([restartNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have _hk3 := hk3
  refine etcd_adequate_members (GF := restartNGF) (hAsLit := etcd_restartN.restartNAddrs_lit k hk)
    (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.restartN.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Main) #(W64 (k : Int)))
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) (etcd_restartN.restartNAddrs k)
    (etcd_restartN.restartNAddrs_nodup k hk) (etcd_restartN.restartNDirs k)
    (etcd_restartN.restartNDirs_nodup k hk) (etcd_restartN.startAddrs k) []
    (etcd_restartN.restartNAddrs_perm k) (etcd_restartN.restartNDirs_perm k)
    σ g ⟨trivial, trivial, trivial⟩ ⟨trivial, Hfs, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC restartNGF := heapAtRN hG lctx
  haveI := Hctx hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.restartN.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.restartN.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Hms, -⟩
  unfold etcd_restartN.startAddrs
  rw [BigSepL.bigSepL_map]
  haveI : ThreadBoundLe restartNGF (2 ^ 28) := ⟨by rw [HT]; word⟩
  haveI : ReceiptBoundLe restartNGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
  haveI : ReceiptBoundLe restartNGF (n + 1) := ⟨by rw [HN]; omega⟩
  have hM := etcd_restartN.wp_Main (GF := restartNGF) k n ids ps ctxs boot hk Hlen Hbf
    (srvLevels_of_max HT) (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hdbo
  wp_apply hM $$ [Hms Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
