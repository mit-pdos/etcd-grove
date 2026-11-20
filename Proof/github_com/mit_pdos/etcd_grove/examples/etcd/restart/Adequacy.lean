/- Lean-first (no Rocq counterpart).

# restart3's closed theorem (restart3 C4, 2026-11-15)

The adequacy of `restart3`'s program (`examples/etcd/restart`), restart1's (`restart1/Adequacy.lean`)
for three members, one of them stopped and restarted in process: `etcd_adequate_members` with the
members' start bundles (each data directory, each peer address; no client address is served), the
read package's two metric names, the trivial extension and the ghost-state bundle `restart3GF`, from
`restart`'s `wp_initialize'` and `etcd_restart.wp_Main` (`MainLinked.lean`). The statement, its
hypotheses and what it does not say: `Results.lean`'s `etcd_restart3_safe`.

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
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.InitLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0. -/
def restart3GF_allG : AllG restart3GF := ⟨⟨0, rfl⟩⟩

instance restart3GF_gooseGpreS : GooseGpreS restart3GF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨restart3GF_allG⟩, ⟨restart3GF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := restart3GF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **The three-member restart example is safe** (`Results.lean`'s `etcd_restart3_safe`, with its
docstring): every real execution of `restart3Program` from a fresh state with one thread, of `n`
steps: if the main thread has finished, its result is `#()`; no thread is stuck; no thread has ended
in a panic. -/
theorem etcd_restart3_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restart3GF, ContextReadErrs (GF := restart3GF) (hG := heapAtR3 hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_restart.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart3Program restart3Names)
    (HAs : addrsUnclaimed restart3Program restart3Addrs)
    (HDs : dataDirsAbsent restart3Program
      [(memberDataDir etcd_restart.name₁), (memberDataDir etcd_restart.name₂), (memberDataDir etcd_restart.name₃)])
    (HEnv : verifyEnvOff restart3Program)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC restart3GF,
      ⊢ etcd_restart.premises (GF := restart3GF) (hG := heapAtR3 hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [(memberDataDir etcd_restart.name₁), (memberDataDir etcd_restart.name₂), (memberDataDir etcd_restart.name₃)])
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow (2 ^ 28) n ([restart3Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 12 ≤ 2 ^ 40) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine etcd_adequate_members_below (GF := restart3GF) (hbody := rfl) (HWal := HWal) (hn := by omega) (hAsLit := by decide) (HEnv := HEnv)
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) restart3Addrs (by decide)
    [(memberDataDir etcd_restart.name₁), (memberDataDir etcd_restart.name₂), (memberDataDir etcd_restart.name₃)]
    (by decide)
    -- the members' start bundles: each peer address, no client address
    [(etcd_restart.name₁, ⟨some etcd_restart.peerAddr₁, none⟩),
      (etcd_restart.name₂, ⟨some etcd_restart.peerAddr₂, none⟩),
      (etcd_restart.name₃, ⟨some etcd_restart.peerAddr₃, none⟩)] [] (by decide) (List.Perm.refl _)
    σ g ⟨trivial, trivial, trivial⟩ ⟨trivial, Hfs, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    (2 ^ 28) n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC restart3GF := heapAtR3 hG lctx
  haveI := Hctx hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.restart.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Hms, -⟩
  icases Hms with ⟨Hs₁, Hs₂, Hs₃, -⟩
  haveI : ThreadBoundLe restart3GF (2 ^ 28) := ⟨by rw [HT]; word⟩
  haveI : ReceiptBoundLe restart3GF (2 ^ 48) := ⟨by rw [HN]; omega⟩
  haveI : ReceiptBoundLe restart3GF (n + 1) := ⟨by rw [HN]; omega⟩
  have hM := etcd_restart.wp_Main (GF := restart3GF) n id₁ id₂ id₃ ps ctxs boot Hbf (srvLevels_of_max HT)
    (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hdbo
  wp_apply hM $$ [Hs₁ Hs₂ Hs₃ Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
