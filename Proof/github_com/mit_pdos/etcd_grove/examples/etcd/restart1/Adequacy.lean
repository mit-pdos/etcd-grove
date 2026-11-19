/- Lean-first (no Rocq counterpart).

# restart1's closed theorem (restart S7.5, 2026-11-14)

The adequacy of `restart1`'s program (`examples/etcd/restart1`), putget's (`putget/Adequacy.lean`) for
one member stopped and restarted in process, with no address served and no client:
`etcd_adequate_members` with the member's start bundle (its data directory, no address), the read
package's two metric names, the trivial extension and the ghost-state bundle `restart1GF`, from
`restart1`'s `wp_initialize'` and `etcd_restart1.wp_Main` (`MainLinked.lean`). The statement, its
hypotheses and what it does not say: `Results.lean`'s `etcd_restart1_safe` (frozen, approved by the
user 2026-11-14, `notes/restart-s7-freeze.md`).

**Over Linux files** (2026-11-15, the user's decision (A) on `wal-lean`): the program's extensions are
`[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`: the file extension's own semantics, no premise on
the environment), since `fileutil`'s package initializer, which the server's initialization runs,
probes `F_OFD_GETLK` through `syscall.FcntlFlock` over the file extension; the theorem's one new
premise is the file extension's initial state, `Fs.FsInit` (`Hfs`: the files as on disk, the roots
well formed), so it says that the program runs on a real file system. Until then the extensions were
`TrivialExt.lean`'s `[idIssueExt]`. (wal-link P2, 2026-11-19) The file extension's semantics excludes I/O errors (`etcdFsSem`, `FsExts.lean`: no
file system call that can succeed fails), and the premise `HWal` (`etcdWalAreasInit`) says that each member's
WAL area (`/tmp/etcd-grove-wal/<name>.etcd`, where its dedicated WAL directory is) is a root of the file
extension, present at start with no WAL in it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsExts_semOk

/-! ## The ghost-state bundle -/

/-- The functors (as the register's `registerGF`): the universal camera (`AllG`) at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def restart1GF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def restart1GF_allG : AllG restart1GF := ⟨⟨0, rfl⟩⟩

instance restart1GF_gooseGpreS : GooseGpreS restart1GF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨restart1GF_allG⟩, ⟨restart1GF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := restart1GF_allG

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAtR1 (hG : HeapGS .hasLC restart1GF) (lctx : GoLocalContext) : HeapGS .hasLC restart1GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `restart1`'s initialization, then `Main()`. -/
def restart1Program [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.restart1.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Main) #()

/-- The read package's two metric names, which `restart1`'s initialization registers (`readRegPerm`,
D16). -/
def restart1Names : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- **The one-member restart example is safe** (`Results.lean`'s `etcd_restart1_safe`, with its
docstring): every real execution of `restart1Program` from a fresh state with one thread, of `n`
steps: if the main thread has finished, its result is `#()`; no thread is stuck; no thread has ended
in a panic. -/
theorem etcd_restart1_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC restart1GF, ContextReadErrs (GF := restart1GF) (hG := heapAtR1 hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_restart1.BootFacts id ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart1Program restart1Names)
    (HDs : dataDirsAbsent restart1Program [go!"restart1.etcd"])
    (HEnv : verifyEnvOff restart1Program)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC restart1GF,
      ⊢ etcd_restart1.premises (GF := restart1GF) (hG := heapAtR1 hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [go!"restart1.etcd"])
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([restart1Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine etcd_adequate_members (GF := restart1GF) (hbody := rfl) (HWal := HWal) (hn := by omega) (hAsLit := by decide) (HEnv := HEnv)
    github_com.mit_pdos.etcd_grove.examples.etcd.restart1.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) [] (by decide)
    [go!"restart1.etcd"] (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
    -- the one member's start bundle: no address, its data directory
    [(go!"restart1", {})] [] (List.Perm.refl _) (List.Perm.refl _) σ g ⟨trivial, trivial, trivial⟩
    ⟨trivial, Hfs, trivial⟩ Hlctx Hinit Hthreads HNs (fun _ h => absurd h List.not_mem_nil) HDs
    n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC restart1GF := heapAtR1 hG lctx
  haveI := Hctx hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.restart1.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.restart1.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Hms, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨Hstart, -⟩
  haveI : ThreadBoundLe restart1GF (2 ^ 28) := ⟨by rw [HT]; word⟩
  haveI : ReceiptBoundLe restart1GF (2 ^ 48) := ⟨by rw [HN]; omega⟩
  haveI : ReceiptBoundLe restart1GF (n + 1) := ⟨by rw [HN]; omega⟩
  have hM := etcd_restart1.wp_Main (GF := restart1GF) n id ctxs boot Hbf (srvLevels_of_max HT)
    (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hdbo
  wp_apply hM $$ [Hstart Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
