/- Lean-first (no Rocq counterpart). minibolt's end-to-end crash safety (`BootCrashSafety`,
`BootP1.lean`): the boot program, which initializes the package and runs `BootMinibolt(dir)` at
the start and after every crash, with the crash relation `OsCrash ∧ P1 (dir ++ "/db")`, reaches no
stuck thread and no unrecovered panic. Its adequacy is `osFsQ_crash_adequacyT` (the crash
interpretation keeping the changes in flight).

A generation's precondition (`bootPre`) is the extension's invariant, the file at `dir/db` as the
generation starts with it (`osFileStart`), `Good` (`CrashGood.lean`), and the fresh package
state. Each generation puts the file in its crash invariant (`csInv_alloc`, `dbOk` of the start
state: `start_dbOk`) and runs the package initializer and `BootMinibolt` (`wp_BootMinibolt`,
`BootMinibolt.lean`); after a crash, the crash part opens the old generation's invariant and
takes the file from it (`csInv_crash_keep`), a `Good` file of the new generation. At the first
boot the file is absent.

The specs `wp_BootMinibolt` uses are linked to their proofs (`Open`, `Get`, `Close`, `Commit`,
from the crash-aware proofs of their callees and the crash-free ones of `Link.lean`).

**What is assumed** (hypotheses of `bootCrashSafety`, besides `BootCrashSafety`'s thread bound,
fewer than `2 ^ 30` live threads along the execution, `BootP1.lean`):
* `Hinit_wp`: the package initializer runs from the fresh package state and gives `pkgFacts`
  (the `sync` package initialized, `errFailed`, `errPageSize`, `errMapTooLarge` and `io.EOF`
  set). `BootCrashSafety` does not have it; as for crashlog, its proof needs `wp_initialize'` of
  `os`, `syscall` and their imports, which are not generated.
* The hand-written `os.file` and `os.fileStat` field facts, as instance hypotheses (as for every
  `OpenFile` and `Stat` spec).

**The thread bound.** `Open.specCrash` needs the thread bound `2 ^ 30` (`ThreadBoundLe`: the
reader pool of `mmaplock`), which the adequacy theorem gives from its `T`, under its hypothesis that
the execution keeps fewer than `T` live threads (`RealCrashThreadsBelow`), as every Perennial
adequacy theorem does. `BootCrashSafety` states that hypothesis at `T = 2 ^ 30`. (The boot program
forks no thread, so it holds of every execution; the time-receipt bound `N` is chosen per
execution, as no proof fixes it.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.BootMinibolt
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.BootP1
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.OpenCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__CommitCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commitCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__GetCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__CloseCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__closeCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__initCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Link
public import GooseLang.Ext.OsFs.CrashQT

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

/-! ## The crash-aware specs, linked -/

section links
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]
variable [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

theorem DB.wp_munmapC : DB.munmap.specCrash (GF := GF) (hG := hG) :=
  DB.munmap.wp_proof_crash golang_org.x.sys.unix.Munmap.wp_proof_crashS

theorem DB.wp_mmapC : DB.mmap.specCrash (GF := GF) (hG := hG) :=
  DB.mmap.wp_proof_crash DB.wp_munmapC wp_mmapSize os.File.wp_Fd
    golang_org.x.sys.unix.Mmap.wp_proof_crashS golang_org.x.sys.unix.wp_Madvise
    golang_org.x.sys.unix.Munmap.wp_proof_crashS wp_pageAt Page.wp_meta

theorem DB.wp_initC : DB.init.specCrash (GF := GF) (hG := hG) :=
  DB.init.wp_proof_crash wp_initPages os.File.WriteAt.wp_proof_crashS os.File.wp_Fd
    syscall.Fdatasync.wp_proof_crashS

theorem wp_OpenC : Open.specCrash (GF := GF) (hG := hG) :=
  Open.wp_proof_crash os.OpenFile.wp_proof_crashS os.File.wp_Name wp_flock os.File.wp_Stat
    os.fileStat.wp_Size os.File.wp_Close DB.wp_close DB.wp_readPageSize DB.wp_initC DB.wp_mmapC

theorem DB.wp_closeC : DB.close.specCrash (GF := GF) (hG := hG) :=
  DB.close.wp_proof_crash DB.wp_munmapC os.File.wp_Fd syscall.wp_Flock os.File.wp_Close

theorem DB.wp_CloseC : DB.Close.specCrash (GF := GF) (hG := hG) :=
  DB.Close.wp_proof_crash DB.wp_closeC

theorem DB.wp_GetC : DB.Get.specCrash (GF := GF) (hG := hG) :=
  DB.Get.wp_proof_crash DB.wp_meta wp_pageAt

theorem DB.wp_commitC : DB.commit.specCrash (GF := GF) (hG := hG) :=
  DB.commit.wp_proof_crash DB.wp_mmapC os.File.Truncate.wp_proof_crashS os.File.Sync.wp_proof_crashS
    wp_pageAt os.File.WriteAt.wp_proof_crashS os.File.wp_Fd syscall.Fdatasync.wp_proof_crashS
    Page.wp_meta Meta.wp_write

theorem DB.wp_CommitC : DB.Commit.specCrash (GF := GF) (hG := hG) :=
  DB.Commit.wp_proof_crash DB.wp_meta DB.wp_commitC

/-- The package initializer's spec (an assumption of `bootCrashSafety`: see the file header). -/
abbrev initialize'.spec : Prop :=
  {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
    (App (Val initialize') (Val #()))
  {{ RET #(); pkgFacts (GF := GF) }}

end links

/-! ## The adequacy -/

attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs

/-- A generation's file starts `Good`: its start state is `dbOk`. -/
theorem start_dbOk (p : GoString) (fo : Option OsFile) (hg : Good fo) : dbOk p (csStart fo) := by
  cases fo with
  | none => intro fo' h _; cases h; trivial
  | some f => exact start_okS (openStart_start (some f) hg)

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A ghost-state instance at the local context `lctx` (the hypotheses are stated over every
instance whose Go local context is the semantics' own). -/
abbrev heapAt (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-- The precondition of the boot program in the generation `L`. -/
def bootPre [G : GooseGlobalGS .hasLC GF] (dir : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ (∃ fo, ⌜Good fo⌝ ∗ osFileStart (L := L) (dir ++ go!"/db") fo) ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

/-- `bootCrashSafety` for executions of fewer than `N` steps along which fewer than `T ≤ 2 ^ 30`
threads are live. -/
theorem bootCrashSafety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    [hPre : GooseGpreS GF]
    (Hinit_wp : ∀ hG : HeapGS .hasLC GF, initialize'.spec (GF := GF) (hG := heapAt hG lctx))
    (N T : Nat) (hT : T ≤ 2 ^ 30) (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hfile : (extLocal osFsExt σ.world).files !! (dir ++ go!"/db") = some none)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : @RealCrashNsteps osFsExts (osFsExtsSemanticsWith (P1 (dir ++ go!"/db"))) _
      (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : @RealCrashThreadsBelow osFsExts (osFsExtsSemanticsWith (P1 (dir ++ go!"/db"))) _
      (boot dir) T n ([boot dir], ((σ, g) : CfgState))) :
    (∀ e2, e2 ∈ t2 →
        @RealNotStuck osFsExts (osFsExtsSemanticsWith (P1 (dir ++ go!"/db"))) _ e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have h := osFsQ_crash_adequacyT (GF := GF) (P1 (dir ++ go!"/db")) N T (boot dir) σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPre dir L)
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · exact h.2
  · -- the first generation: the file is absent
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Hgs
    icases (BigSepM.bigSepM_lookup (Φ := fun p fo => osFileStart (L := hG.goose_localGS) p fo)
      Hfile) $$ Hfs with Hf
    imodintro
    unfold bootPre
    iframe Hos Hgs
    iexists none
    iframe Hf
    ipureintro; trivial
  · -- every generation: the file in its invariant, the boot program, and the next generation's
    intro hG _ HT Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, σ.goState.goLctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    haveI : ThreadBoundLe GF (2 ^ 30) := ⟨by rw [HT]; exact hT⟩
    unfold bootPre
    iintro ⟨#Hos, ⟨%fo0, %hg0, Hf⟩, Hgs⟩ Htok
    imod csInv_alloc (L := hG.goose_localGS) dbCrashN (dir ++ go!"/db") (dbOk (dir ++ go!"/db"))
      fo0 (start_dbOk _ fo0 hg0) $$ Hf with ⟨%γ, #Hinv, Hown⟩
    imodintro
    isplitl [Hgs Hown Htok]
    · -- the boot program
      unfold boot
      wp_apply (Hinit_wp hG) $$ Hgs as #Hpkg
      wp_pures
      wp_apply wp_BootMinibolt wp_OpenC DB.wp_GetC DB.wp_CommitC DB.wp_CloseC dir γ
          fo0 hg0 $$ [Hown Htok]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: take the file from the old generation's invariant
      iintro %L' _ #Hos' Hr Hgs'
      unfold csInv
      imod inv_acc (E := ⊤) (show ↑dbCrashN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%s, >Hv, >Hs, >%Hok⟩
      icases csInv_crash_keep (P1 (dir ++ go!"/db")) hG.goose_localGS L' [] (dir ++ go!"/db")
          List.not_mem_nil Good s Hok $$ Hr Hs with ⟨%fo', %hg', Hf', -, Hs⟩
      imod Hclose $$ [Hv Hs] with -
      · inext; iexists s; iframe; ipureintro; exact Hok
      imodintro
      iframe Hos' Hgs'
      iexists fo'
      iframe Hf'
      ipureintro; exact hg'

/-- **minibolt's crash safety** (`BootCrashSafety`, `BootP1.lean`: executions along which fewer
than `2 ^ 30` threads are live), under the hypotheses of the file header: the package initializer
(`Hinit_wp`) and the `os.file`/`os.fileStat` field instances. -/
theorem bootCrashSafety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (dir : GoString)
    (Hinit_wp : ∀ hG : HeapGS .hasLC osFsGF,
      initialize'.spec (GF := osFsGF) (hG := heapAt hG lctx)) :
    BootCrashSafety dir := by
  intro σ g Hlctx Hpkgs Hinit Hfile Hthreads n κs t2 σ2 b Hsteps Hlive
  exact bootCrashSafety_bounded (GF := osFsGF) Hinit_wp (n + 1) (2 ^ 30) (Nat.le_refl _)
    σ g dir Hlctx Hpkgs Hinit Hfile n κs t2 σ2 b Hsteps (by omega) Hthreads Hlive

end adequacy

end bboltfs
end EtcdGrove
end Perennial
