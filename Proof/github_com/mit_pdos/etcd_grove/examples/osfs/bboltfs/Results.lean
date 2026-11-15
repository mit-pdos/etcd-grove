/- Lean-first (no Rocq counterpart). minibolt's end-to-end crash safety (`BootCrashSafety`,
`BootP1.lean`): the boot program, which initializes the package and runs `BootMinibolt(dir)` at
the start and after every crash, over the Linux file extension's per-byte semantics with P1 as the
crash filter and every step allowed (`fsExtsSemanticsWithS AnyStep P1`), reaches no stuck thread
and no unrecovered panic. Its adequacy is `fsSQ_crash_adequacy` (with `anyStep_keeps`).

A generation's precondition (`bootPre`) is the extension's invariant, the whole of the tree's history
with nothing logged, the file at `dir/db` as the generation starts with it (`StartSt`: absent, or as
on disk and `Good`), and the fresh package state. Each generation puts the file in its crash
invariant (`csInv_alloc`, `dbOk` of the start state: `start_okS`) and runs the package initializer
and `BootMinibolt` (`wp_BootMinibolt`); after a crash, the crash part opens the old generation's
invariant and takes the file and the history from it (`csInv_crash_keep`): a `Good` file of the new
generation, as on disk. At the first boot the file is absent.

The specs `wp_BootMinibolt` uses are linked to their proofs (`Open`, `Get`, `Close`, `Commit`, from
the crash-aware proofs of their callees, `Proof/os/CrashStSpec.lean`'s `*.wp_proof_crashS`, and the
crash-free ones of `Link.lean`).

**What is assumed** (hypotheses of `bootCrashSafety`, besides `BootCrashSafety`'s thread bound):
* `Hinit_wp`: the package initializer runs from the fresh package state and gives `pkgFacts`; as
  for crashlog, its proof needs `wp_initialize'` of `os`, `syscall` and their imports, which are
  not generated.
* The hand-written `os.file` and `os.fileStat` field facts, as instance hypotheses (as for every
  `OpenFile` and `Stat` spec).

The premises are satisfiable and not vacuous: an empty root is a start state
(`GooseLang/Ext/Fs/TestsInit.lean`), and P1 always leaves a crash (`P1Sat.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.BootMinibolt
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.BootP1
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.P1Sat
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.OpenCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__CommitCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__commitCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__GetCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__CloseCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__closeCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__initCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__munmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Link
public import Proof.os.CrashStSpec
public import GooseLang.Ext.Fs.AdequacyS

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

/-! ## The crash-aware specs, linked -/

section links
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]
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

/-- The root `d` names its directory, whatever the history. -/
theorem lookupH_root {R : Roots} (hr : RootsOk R) {d : GoString} {j : Ino} (hd : (d, j) ∈ R)
    (V : Hist) : lookupH R V d = some (.dir j) := by
  have := lookup_joinPath (st := Hist.st R V) hr hd (cs := []) (by simp)
  simp only [joinPath, List.flatMap_nil, List.append_nil, walk] at this
  exact this

/-- A history with nothing logged has no other crash. -/
theorem treeCrashed_nil {m : Tree} {V' : Hist} (h : TreeCrashed (m, []) V') : V' = (m, []) := by
  obtain ⟨n, hn, rfl⟩ := h
  simp only [List.length_nil, Nat.le_zero] at hn; subst hn; rfl

/-- The start state's crash obligation: `dbOk`. -/
theorem startSt_okS [GooseExts] {s : CState} (hs : StartSt s) : dbOk s := by
  rcases hs with rfl | ⟨i, vs, sz, rfl, hg⟩
  · trivial
  · exact start_okS (i := i) (openStart_disk vs sz hg)

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- **A generation's file starts `Good`**: what `startAt` gives of a history with nothing logged,
the file `Good`, is a start state (`StartSt`), as `csInv_alloc` takes it. -/
theorem startAt_startSt [L : GooseLocalGS GF] (p : GoString) (R : Roots) (m : Tree)
    (fo : Option OsFile) (hg : Good fo) :
    startAt L p R (m, []) fo ⊢ ∃ s, ⌜StartSt s ∧ SPathOk p R s (m, []) ∧
      TreeOkI Good p R (sIno s) (m, [])⌝ ∗ csStartRes (L := L) s := by
  unfold startAt
  cases hl : lookupH R (m, []) p with
  | none =>
    iintro %hfo
    subst hfo
    iexists none
    isplitr
    · ipureintro
      refine ⟨.inl rfl, hl, fun V' h => ?_⟩
      rw [treeCrashed_nil h]; exact .inl ⟨hl, trivial⟩
    · unfold csStartRes; iempintro
  | some x =>
    cases x with
    | dir J => iintro %h; exact h.elim
    | file i =>
      iintro ⟨%f, %hfo, Hf⟩
      subst hfo
      obtain ⟨vs, sz, rfl⟩ := hg.2.2
      iexists csStart i (OsFile.ofDisk vs sz)
      isplitr
      · ipureintro
        refine ⟨.inr ⟨i, vs, sz, rfl, hg⟩, hl, fun V' h => ?_⟩
        rw [treeCrashed_nil h]; exact .inr ⟨i, rfl, hl⟩
      · unfold csStartRes
        simp only [csStart]
        iunfold osFileStart at Hf; iexact Hf

end start

attribute [local instance] fsExts fsExtsInterp

/-- `AnyStep` keeps every step. -/
theorem anyStep_keeps : StepKeeps AnyStep := by
  intro _ _ _ _ _ _ _ _ _ _ hs
  exact ⟨_, _, _, hs, trivial⟩

local instance : GooseSemantics := fsExtsSemanticsWithS AnyStep P1
local instance : ExtSemantics fsExt := fsSemWithS AnyStep P1
local instance : HasExt fsExt := fsExtsWithS_hasFs AnyStep P1

/-- The semantics' instances the specs need, over the semantics with P1. -/
abbrev P1Ctx (P : ∀ [GooseSemantics] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Prop) : Prop :=
  letI := fsExtsSemanticsWithS AnyStep P1
  letI := fsSemWithS AnyStep P1
  letI := fsExtsWithS_hasFs AnyStep P1
  haveI : FsSemOk := fsSemWithS_ok AnyStep P1 anyStep_keeps
  P

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A ghost-state instance at the local context `lctx` (the hypotheses are stated over every
instance whose Go local context is the semantics' own). -/
abbrev heapAt (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-- The precondition of the boot program in the generation `L`, `R` the roots. -/
def bootPre [G : GooseGlobalGS .hasLC GF] (R : Roots) (dir : GoString) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (m : Tree) (s : CState), osTree (L := L) (DFrac.own 1) R (m, []) ∗
      ⌜StartSt s ∧ SPathOk (child dir dbB) R s (m, []) ∧
        TreeOkI Good (child dir dbB) R (sIno s) (m, [])⌝ ∗ csStartRes (L := L) s)

/-- `bootCrashSafety` for executions of fewer than `N` steps along which fewer than `T ≤ 2 ^ 30`
threads are live. -/
theorem bootCrashSafety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    [hPre : GooseGpreS GF]
    (Hinit_wp : P1Ctx fun [_] [_] [_] [_] =>
      ∀ hG : HeapGS .hasLC GF, initialize'.spec (GF := GF) (hG := heapAt hG lctx))
    (N T : Nat) (hT : T ≤ 2 ^ 30) (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnone : (extLocal fsExt σ.world).lookup (child dir dbB) = none)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : @RealCrashNsteps fsExts (fsExtsSemanticsWithS AnyStep P1) _
      (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : @RealCrashThreadsBelow fsExts (fsExtsSemanticsWithS AnyStep P1) _
      (boot dir) T n ([boot dir], ((σ, g) : CfgState))) :
    (∀ e2, e2 ∈ t2 → @RealNotStuck fsExts (fsExtsSemanticsWithS AnyStep P1) _ e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  letI := fsExtsSemanticsWithS AnyStep P1
  letI := fsSemWithS AnyStep P1
  letI := fsExtsWithS_hasFs AnyStep P1
  haveI : FsSemOk := fsSemWithS_ok AnyStep P1 anyStep_keeps
  obtain ⟨j, hrj⟩ := Hdir
  have hR : RootsOk (extLocal fsExt σ.world).fs.roots := Hinit.2.2.2.1
  have hl0 : (extLocal fsExt σ.world).lookup (child dir dbB) =
      lookupH (extLocal fsExt σ.world).fs.roots ((extLocal fsExt σ.world).fs.treeDur, [])
        (child dir dbB) := by
    rw [lookupH_eq, Hinit.2.1]
  rw [hl0] at Hnone
  obtain ⟨R, hRdef⟩ : ∃ R, (extLocal fsExt σ.world).fs.roots = R := ⟨_, rfl⟩
  rw [hRdef] at hR hrj Hnone
  obtain ⟨m0, hm0⟩ : ∃ m0, (extLocal fsExt σ.world).fs.treeDur = m0 := ⟨_, rfl⟩
  rw [hm0] at Hnone
  have h := fsSQ_crash_adequacy (GF := GF) AnyStep P1 anyStep_keeps N T (boot dir) σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPre R dir L)
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · exact h.2
  · -- the first generation: the tree as on disk, the file absent
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos - Ht Hgs
    rw [hRdef, hm0]
    unfold bootPre
    imodintro
    iframe Hos Hgs
    iexists m0, none
    iframe Ht
    isplitr
    · ipureintro
      refine ⟨.inl rfl, Hnone, fun V' h => ?_⟩
      rw [treeCrashed_nil h]; exact .inl ⟨Hnone, trivial⟩
    · unfold csStartRes; iempintro
  · -- every generation: the file in its invariant, the boot program, and the next generation's
    intro hG _ HT Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    haveI : ThreadBoundLe GF (2 ^ 30) := ⟨by rw [HT]; exact hT⟩
    unfold bootPre
    iintro ⟨#Hos, Hgs, %m, %s, Ht, %hso, Hsr⟩ Htok
    obtain ⟨hst, hp, htr⟩ := hso
    have hwf : CsWf s := by
      rcases hst with rfl | ⟨i, vs, sz, rfl, -⟩
      · trivial
      · exact csStart_wf i _
    have hidle : ∀ i x, s = some (i, x) → x.busy = .idle ∧ x.fb ≤ x.fa := by
      rcases hst with rfl | ⟨i, vs, sz, rfl, -⟩
      · intro _ _ h; cases h
      · intro _ _ h; simp only [csStart, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨rfl, Nat.le_refl _⟩
    have hcut : CsCut s := by
      rcases hst with rfl | ⟨i, vs, sz, rfl, -⟩
      · trivial
      · exact csStart_cut i _
    imod csInv_alloc (L := hG.goose_localGS) dbCrashN (child dir dbB) R (m, []) Good dbOk s hidle
      (startSt_okS hst) htr hwf hcut hp $$ Ht Hsr with ⟨%γ, #Hinv, Hown⟩
    imodintro
    isplitl [Hgs Hown Htok]
    · -- the boot program
      unfold boot
      wp_apply (Hinit_wp hG) $$ Hgs as #Hpkg
      wp_pures
      wp_apply wp_BootMinibolt wp_OpenC DB.wp_GetC DB.wp_CommitC DB.wp_CloseC dir R (m, []) j γ s
          (lookupH_root hR hrj _) hst $$ [Hown Htok]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: take the file and the history from the old generation's invariant
      iintro %L' %V' _ #Hos' Hr Hgs'
      unfold csInv
      imod inv_acc (E := ⊤) (show ↑dbCrashN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%s', %W, >Hv, >Hs, >Ht, >%Hok⟩
      icases csInv_crash_keep P1 hG.goose_localGS L' [] V' (child dir dbB) R Good s' W
          (fun _ _ => List.not_mem_nil) Hok.2.1 (fun i x h => by subst h; exact Hok.1) Hok.2.2 $$ Hr Hs Ht
        with ⟨%fo', %hgt, Ht', Hst, -, Hs, Ht⟩
      obtain ⟨hg', htc'⟩ := hgt
      imod Hclose $$ [Hv Hs Ht] with -
      · inext; iexists s', W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hos' Hgs'
      rcases V' with ⟨m', l'⟩
      obtain rfl : l' = [] := treeCrashed_log htc'
      icases startAt_startSt (L := L') (child dir dbB) R m' fo' hg' $$ Hst with ⟨%s2, %hs2, Hs2⟩
      iexists m', s2
      iframe Ht' Hs2
      ipureintro; exact hs2

/-- **minibolt's crash safety** (`BootCrashSafety`, `BootP1.lean`: executions along which fewer
than `2 ^ 30` threads are live), under the hypotheses of the file header: the package initializer
(`Hinit_wp`) and the `os.file`/`os.fileStat` field instances. -/
theorem bootCrashSafety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (dir : GoString)
    (Hinit_wp : P1Ctx fun [_] [_] [_] [_] =>
      ∀ hG : HeapGS .hasLC fsGF, initialize'.spec (GF := fsGF) (hG := heapAt hG lctx)) :
    BootCrashSafety dir := by
  intro σ g Hlctx Hpkgs Hinit Hdir Hnone Hthreads n κs t2 σ2 b Hsteps Hlive
  exact bootCrashSafety_bounded (GF := fsGF) Hinit_wp (n + 1) (2 ^ 30) (Nat.le_refl _)
    σ g dir Hlctx Hpkgs Hinit Hdir Hnone n κs t2 σ2 b Hsteps (by omega) Hthreads Hlive

end adequacy

#print axioms bootCrashSafety
-- P1 is never vacuous at a crash, and a file no change touched never makes it fail (`P1Sat.lean`).
#print axioms P1Sat.p1_crash_exists
#print axioms P1Sat.p1_untouched

end osfs_bboltfs
end EtcdGrove
end Perennial

end
