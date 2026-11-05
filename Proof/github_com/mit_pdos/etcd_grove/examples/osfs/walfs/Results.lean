/-
The end-to-end result of `examples/osfs/walfs`'s `segdir.go`: the crash adequacy of its boot
program, which initializes the package and runs `Boot(dir)`, at the start and after every crash,
over the Linux file extension with the namespace (`osFs_crash_adequacyN`, the crash interpretation
that keeps a prefix of each directory's changes since its last commit).

The boot program's precondition, over a generation's local ghost state `L` (`bootPre`), is `L`'s
invariant of the mapped cells, the in-flight flag unset, `dir`'s whole ghost entry with nothing in
flight, in which neither `seg` nor `seg.tmp` is a directory, and, if `seg` names a file, that file
as `L` starts with it (`osFileStart`), `DataGood` (absent, or the data). Each generation puts half
of `dir`'s entry and of the file in its crash invariant (`bootInv`) and runs `Boot` (`Boot.lean`'s
`wp_Boot`). After a crash, the crash part opens the old generation's invariant: the new entry of
`dir` is a crash outcome of the old one (`osNsCrash_take`), so `seg` and `seg.tmp` are no
directories and `seg` is absent or names the invariant's key; that key's file in the new
generation is a crash of the invariant's half (`osCrashT_take_runs_keep`), so `DataGood`.

**What is assumed**, as for `examples/osfs/crashlog`: the package initializer (`Hinit_wp`, which
needs `wp_initialize'` of this repository's `os` and `syscall`), and the hand-written `os.file`
field facts (instance hypotheses). The trust base is otherwise the extension's semantics
(`GooseLang/Ext/OsFs/Impl.lean`) and the trusted models of `os` and `syscall`
(`TrustedCode/os.lean`, `TrustedCode/syscall.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot
public import Proof.os.File__ReadAt
public import Proof.os.File__WriteAt
public import Proof.os.File__Fd
public import Proof.os.File__Close
public import Proof.syscall.Fdatasync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs
  osFsExtsCrashInterpN

/-- The boot program: initialize the package, then call `Boot(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Boot []))) (Val #())) (Val #dir))

section gen
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- The file of `seg`'s key `ko` as the generation `L` starts with it: `DataGood`. -/
def startFile (L : GooseLocalGS GF) : Option GoString → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ fo, ⌜DataGood fo⌝ ∗ osFileStart (L := L) k fo)

/-- The precondition of the boot program in the generation `L`. -/
def bootPre (dir : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ osNsBusy (L := L) false ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (g : DirG) (ko : Option GoString), osDir (L := L) dir (DFrac.own 1) g ∗
      ⌜g.pend = [] ∧ NoDirs g ∧ SegOut g ko⌝ ∗ startFile L ko)

/-- A `DataGood` file as a generation starts with it, split between the invariant and the
program. -/
theorem startFile_split (L : GooseLocalGS GF) (k : GoString) (fo : Option OsFile) (hg : DataGood fo) :
    osFileStart (L := L) k fo ⊢ keyRes (L := L) (some k) ∗
      ∃ (mo : Option OsMeta) (bs : List (w8 × Bool)),
        osMeta (L := L) k (DFrac.own (1 : Qp).half) mo ∗
        osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜CheckOk mo bs⌝ := by
  cases fo with
  | none =>
    iintro Hm
    unfold osFileStart
    icases (osMeta_halves (L := L) k none).1 $$ Hm with ⟨Hm1, Hm2⟩
    unfold keyRes
    isplitl [Hm1]
    · iexists none, []
      iframe Hm1
      isplitr
      · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; intro fo' h; cases h; intro f hf; cases hf
    · iexists none, []
      iframe Hm2
      isplitr
      · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; intro m hm; cases hm
  | some f =>
    unfold osFileStart
    iintro ⟨Hm, Hb⟩
    icases (osMeta_halves (L := L) k _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves (L := L) k 0 _).1 $$ Hb with ⟨Hb1, Hb2⟩
    unfold keyRes
    have hd : f.cur = dataC := hg f rfl
    isplitl [Hm1 Hb1]
    · iexists (some (initMeta f)), (f.cur.map (·, true))
      iframe Hm1 Hb1
      ipureintro; exact start_good (some f) hg
    · iexists (some (initMeta f)), (f.cur.map (·, true))
      iframe Hm2 Hb2
      ipureintro
      intro m hm
      cases hm
      refine ⟨by simp [initMeta, hd, dataC], by simp [hd, dataC], ?_⟩
      rw [List.map_map]; exact (List.map_id'' (fun _ => rfl) _).trans hd

theorem startFile_res [hG : HeapGS .hasLC GF] (ko : Option GoString) :
    startFile hG.goose_localGS ko ⊢ keyRes (L := hG.goose_localGS) ko ∗ segRes (GF := GF) ko := by
  cases ko with
  | none => unfold startFile keyRes segRes; dsimp only; iintro -; isplitl [] <;> iempintro
  | some k =>
    unfold startFile
    iintro ⟨%fo, %hg, Hf⟩
    unfold segRes
    iapply startFile_split hG.goose_localGS k fo hg $$ Hf

end gen

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `crash_safety` for executions of fewer than `N` steps along which fewer than `T` threads are
live. -/
theorem crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions]
    [hPre : GooseGpreS GF]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC GF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (N T : Nat) (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hdir : (extLocal osFsExt σ.world).ns !! dir = some .dir)
    (Hnd : (extLocal osFsExt σ.world).ns !! child dir segB ≠ some .dir ∧
      (extLocal osFsExt σ.world).ns !! child dir tmpB ≠ some .dir)
    (Hseg : ∀ k, (extLocal osFsExt σ.world).ns !! child dir segB = some (.file k) →
      ∃ fo, (extLocal osFsExt σ.world).files !! k = some fo ∧ DataGood fo)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (boot dir) T n ([boot dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine osFs_crash_adequacyN (GF := GF) N T (boot dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPre dir L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the directory and the file as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Hds Hz Hgs
    have hdm : dirMap (extLocal osFsExt σ.world) !! dir =
        some ⟨entsOf (extLocal osFsExt σ.world).ns dir, []⟩ := by
      rw [dirMap_lookup, if_pos Hdir]
    icases (BigSepM.bigSepM_lookup
      (Φ := fun d g => osDir (L := hG.goose_localGS) d (DFrac.own 1) g) hdm) $$ Hds with Hd
    have hnd0 : NoDirs ⟨entsOf (extLocal osFsExt σ.world).ns dir, []⟩ := fun e he => by
      rw [crashTo_nil rfl he]
      exact ⟨by rw [entsOf_child _ _ _ segB_ok]; exact Hnd.1,
        by rw [entsOf_child _ _ _ tmpB_ok]; exact Hnd.2⟩
    unfold bootPre
    imodintro
    iframe Hos Hz Hgs
    cases hsk : (extLocal osFsExt σ.world).ns !! child dir segB with
    | none =>
      iexists _, none
      iframe Hd
      isplitr
      · ipureintro
        refine ⟨rfl, hnd0, fun e he => .inl ?_⟩
        rw [crashTo_nil rfl he]
        show entsOf _ dir !! segB = none
        rw [entsOf_child _ _ _ segB_ok]; exact hsk
      unfold startFile; iempintro
    | some x =>
      cases x with
      | dir => exact absurd hsk Hnd.1
      | file k =>
      obtain ⟨fo, hfo, hgood⟩ := Hseg k hsk
      icases (BigSepM.bigSepM_lookup
        (Φ := fun p fo => osFileStart (L := hG.goose_localGS) p fo) hfo) $$ Hfs with Hf
      iexists _, (some k)
      iframe Hd
      isplitr
      · ipureintro
        refine ⟨rfl, hnd0, fun e he => .inr ⟨k, rfl, ?_⟩⟩
        rw [crashTo_nil rfl he]
        show entsOf _ dir !! segB = _
        rw [entsOf_child _ _ _ segB_ok]; exact hsk
      unfold startFile
      iexists fo
      iframe Hf
      ipureintro; exact hgood
  · -- every generation: the invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPre
    iintro ⟨#Hos, Hz, Hgs, %g0, %ko0, Hd, %hp, Hsf⟩ _
    imod ghostVar_alloc (GF := GF) ko0 with ⟨%γ, Hv⟩
    icases (ghostVar_split_half (A := Option GoString) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases (osDir_halves (L := hG.goose_localGS) dir g0).1 $$ Hd with ⟨Hd1, Hd2⟩
    icases startFile_res ko0 $$ Hsf with ⟨Hk, Hs⟩
    imod inv_alloc bootN ⊤ (iprop(∃ (g : DirG) (ko : Option GoString),
        osDir (L := hG.goose_localGS) dir (DFrac.own (1 : Qp).half) g ∗
        ghostVar γ (1 : Qp).half ko ∗ ⌜NoDirs g ∧ SegOut g ko⌝ ∗
        keyRes (L := hG.goose_localGS) ko)) $$ [Hd2 Hv1 Hk] with #Hinv
    · inext; iexists g0, ko0; iframe; ipureintro; exact hp.2
    imodintro
    isplitl [Hgs Hd1 Hz Hv2 Hs]
    · -- the boot program
      unfold boot
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_Boot os.File.ReadAt.wp_proof os.File.Close.wp_proof os.File.WriteAt.wp_proof
          os.File.Fd.wp_proof syscall.Fdatasync.wp_proof dir γ g0 ko0 hp.1 hp.2.1 hp.2.2
          $$ [Hd1 Hz Hv2 Hs]
      · iframe; iframe #; unfold bootInv; iexact Hinv
      ipureintro; rfl
    · -- after a crash: the directory and the file from the old generation's invariant
      iintro %L' _ #Hos' Hr Hn Hz' Hgs'
      imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%g, %ko, >Hd, >Hv, >%Hp, >Hk⟩
      icases osNsCrash_take hG.goose_localGS L' [] dir List.not_mem_nil _ g $$ Hn Hd
        with ⟨%g', %hg', Hd', -, Hd⟩
      obtain ⟨hpend, hcr⟩ := hg'
      have hnd' : NoDirs g' := fun e he => by rw [crashTo_nil hpend he]; exact Hp.1 _ hcr
      rcases Hp.2 _ hcr with hnone | ⟨k, rfl, hk⟩
      · imod Hclose $$ [Hd Hv Hk] with -
        · inext; iexists g, ko; iframe; ipureintro; exact Hp
        imodintro
        try unfold bootPre
        iframe Hos' Hz' Hgs'
        iexists g', none
        iframe Hd'
        isplitr
        · ipureintro
          exact ⟨hpend, hnd', fun e he => .inl (by rw [crashTo_nil hpend he]; exact hnone)⟩
        unfold startFile; iempintro
      · try unfold keyRes
        dsimp only
        icases Hk with ⟨%mo, %bs, Hm, Hb, %hgood⟩
        icases osCrashT_take_runs_keep hG.goose_localGS L' [] k List.not_mem_nil _ mo
          [(0, DFrac.own (1 : Qp).half, bs)] $$ Hr Hm [Hb] with ⟨%fo, %hfc, Hf, -, Hm, Hb⟩
        · iapply BigSepL.bigSepL_singleton.2; iexact Hb
        icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
        imod Hclose $$ [Hd Hv Hm Hb] with -
        · inext; iexists g, (some k); iframe Hd Hv
          isplitr
          · ipureintro; exact Hp
          dsimp only
          iexists mo, bs
          iframe
          ipureintro; exact hgood
        imodintro
        try unfold bootPre
        iframe Hos' Hz' Hgs'
        iexists g', (some k)
        iframe Hd'
        isplitr
        · ipureintro
          exact ⟨hpend, hnd', fun e he => .inr ⟨k, rfl, by rw [crashTo_nil hpend he]; exact hk⟩⟩
        unfold startFile
        iexists fo
        iframe Hf
        ipureintro; exact hgood fo hfc

/-- **Crash safety of `examples/osfs/walfs`'s `segdir.Boot`.** In every execution with crashes of
the boot program (`RealCrashNsteps`, the real semantics), from a state whose Go context satisfies
the Go semantics and the package's assumptions, with no package initialized, the main thread only,
the Linux file extension's state as on disk (`OsInit`), `dir` a directory of the namespace, in
which neither `seg` nor `seg.tmp` is a directory and `seg`, if it names a file, names one that is
`DataGood` (the 8 bytes of data): the boot program's result is `#()`, no thread is stuck and no
thread has an unrecovered panic, so `check`'s panic never fires, however many times the node
crashes, and in particular whenever a crash interrupts `commit` (after the create, the write, the
`fdatasync`, the rename or the directory's sync). It assumes that the package's initializer runs
(`Hinit_wp`, the module docstring). (`crash_safety_bounded` with the ghost state `osFsGF`.) -/
theorem crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC osFsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hdir : (extLocal osFsExt σ.world).ns !! dir = some .dir)
    (Hnd : (extLocal osFsExt σ.world).ns !! child dir segB ≠ some .dir ∧
      (extLocal osFsExt σ.world).ns !! child dir tmpB ≠ some .dir)
    (Hseg : ∀ k, (extLocal osFsExt σ.world).ns !! child dir segB = some (.file k) →
      ∃ fo, (extLocal osFsExt σ.world).files !! k = some fo ∧ DataGood fo)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  crash_safety_bounded (GF := osFsGF) Hinit_wp (n + 1) (n + 2) σ g dir Hlctx Hpkgs Hinit Hdir Hnd
    Hseg n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

#print axioms crash_safety

end osfs_walfs
end EtcdGrove
end Perennial
