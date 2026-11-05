/-
The end-to-end result of `examples/osfs/walfs`'s `dirswap.go`: the crash adequacy of its boot
program, which initializes the package and runs `BootDir(dir)`, at the start and after every
crash, over the Linux file extension with the namespace (`osFs_crash_adequacyN`, the crash
interpretation that keeps a prefix of the namespace's operations since its last commit).

The boot program's precondition, over a generation's local ghost state `L` (`bootPreDS`), is `L`'s
invariant of the mapped cells, the in-flight flag unset, the whole history of the namespace with
nothing logged, whose namespace is `Safe` (`DirSwap.lean`) with some key `ko`, and that key's file
as `L` starts with it (`osFileStart`), `DataGood`. Each generation puts half of the history and of
the file in its crash invariant (`dsInv`) and runs `BootDir` (`wp_BootDir`). After a crash, the
crash part opens the old generation's invariant: the new namespace is a prefix of the old history
replayed (`osNsCrash_takeAll`), so `Safe` with the invariant's key, whose file in the new
generation is a crash of the invariant's half (`osCrashT_take_runs_keep`), so `DataGood`.

**What is assumed**, as for `segdir`'s result (`Results.lean`): the package initializer
(`Hinit_wp`) and the hand-written `os.file` field facts (instance hypotheses).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwap
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Results
public import Proof.os.File__Sync

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

/-- The boot program: initialize the package, then call `BootDir(dir)`. -/
def bootDS [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve BootDir []))) (Val #())) (Val #dir))

section gen
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- The precondition of the boot program in the generation `L`. -/
def bootPreDS (dir : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ osNsBusy (L := L) false ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (ns : NsMap) (ko : Option GoString), osNsAll (L := L) (DFrac.own 1) (ns, []) ∗
      ⌜Safe dir ko ns⌝ ∗ startFile L ko)

end gen

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `dirswap_crash_safety` for executions of fewer than `N` steps along which fewer than `T`
threads are live. -/
theorem dirswap_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [os.Assumptions] [os.file.FieldAssumptions]
    [hPre : GooseGpreS GF]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC GF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (N T : Nat) (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hsafe : Safe dir none (extLocal osFsExt σ.world).ns ∨
      ∃ k, Safe dir (some k) (extLocal osFsExt σ.world).ns ∧
        ∃ fo, (extLocal osFsExt σ.world).files !! k = some fo ∧ DataGood fo)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootDS dir) n ([bootDS dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (bootDS dir) T n ([bootDS dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine osFs_crash_adequacyN (GF := GF) N T (bootDS dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPreDS dir L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the namespace and the file as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Hds Hz Hgs
    unfold bootPreDS
    imodintro
    iframe Hos Hz Hgs
    rcases Hsafe with hs | ⟨k, hs, fo, hfo, hgood⟩
    · iexists _, none
      iframe Hds
      isplitr
      · ipureintro; exact hs
      unfold startFile; iempintro
    · icases (BigSepM.bigSepM_lookup
        (Φ := fun p fo => osFileStart (L := hG.goose_localGS) p fo) hfo) $$ Hfs with Hf
      iexists _, (some k)
      iframe Hds
      isplitr
      · ipureintro; exact hs
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
    unfold bootPreDS
    iintro ⟨#Hos, Hz, Hgs, %ns0, %ko0, HV, %hs, Hsf⟩ _
    imod ghostVar_alloc (GF := GF) ko0 with ⟨%γ, Hv⟩
    icases (ghostVar_split_half (A := Option GoString) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases (osNsAll_halves (L := hG.goose_localGS) (ns0, [])).1 $$ HV with ⟨HV1, HV2⟩
    icases startFile_res ko0 $$ Hsf with ⟨Hk, Hs⟩
    have hsh : SafeH dir ko0 (ns0, []) := fun n => by
      show Safe dir ko0 (nsReplay (([] : List NsOp).take n) ns0)
      simp only [List.take_nil]; exact hs
    imod inv_alloc bootN ⊤ (iprop(∃ (V : NsMap × List NsOp) (ko : Option GoString),
        osNsAll (L := hG.goose_localGS) (DFrac.own (1 : Qp).half) V ∗
        ghostVar γ (1 : Qp).half ko ∗ ⌜SafeH dir ko V⌝ ∗
        keyRes (L := hG.goose_localGS) ko)) $$ [HV2 Hv1 Hk] with #Hinv
    · inext; iexists (ns0, []), ko0; iframe; ipureintro; exact hsh
    imodintro
    isplitl [Hgs HV1 Hz Hv2 Hs]
    · -- the boot program
      unfold bootDS
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_BootDir os.File.ReadAt.wp_proof os.File.Close.wp_proof os.File.WriteAt.wp_proof
          os.File.Sync.wp_proof dir γ ns0 ko0 hs $$ [HV1 Hz Hv2 Hs]
      · iframe; iframe #; unfold dsInv; iexact Hinv
      ipureintro; rfl
    · -- after a crash: the namespace and the file from the old generation's invariant
      iintro %L' _ #Hos' Hr Hn Hz' Hgs'
      imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%V, %ko, >HV, >Hv, >%Hp, >Hk⟩
      icases osNsCrash_takeAll hG.goose_localGS L' _ V $$ Hn HV with ⟨%n, %hn, HV', HV⟩
      have hs' : Safe dir ko (nsReplay (V.2.take n) V.1) := Hp n
      cases ko with
      | none =>
        imod Hclose $$ [HV Hv Hk] with -
        · inext; iexists V, none; iframe; ipureintro; exact Hp
        imodintro
        try unfold bootPreDS
        iframe Hos' Hz' Hgs'
        iexists _, none
        iframe HV'
        isplitr
        · ipureintro; exact hs'
        unfold startFile; iempintro
      | some k =>
        try unfold keyRes
        dsimp only
        icases Hk with ⟨%mo, %bs, Hm, Hb, %hgood⟩
        icases osCrashT_take_runs_keep hG.goose_localGS L' [] k List.not_mem_nil _ mo
          [(0, DFrac.own (1 : Qp).half, bs)] $$ Hr Hm [Hb] with ⟨%fo, %hfc, Hf, -, Hm, Hb⟩
        · iapply BigSepL.bigSepL_singleton.2; iexact Hb
        icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
        imod Hclose $$ [HV Hv Hm Hb] with -
        · inext; iexists V, (some k); iframe HV Hv
          isplitr
          · ipureintro; exact Hp
          dsimp only
          iexists mo, bs
          iframe
          ipureintro; exact hgood
        imodintro
        try unfold bootPreDS
        iframe Hos' Hz' Hgs'
        iexists _, (some k)
        iframe HV'
        isplitr
        · ipureintro; exact hs'
        unfold startFile
        iexists fo
        iframe Hf
        ipureintro; exact hgood fo hfc

/-- **Crash safety of `examples/osfs/walfs`'s `dirswap.BootDir`.** In every execution with crashes
of the boot program (`RealCrashNsteps`, the real semantics), from a state whose Go context
satisfies the Go semantics and the package's assumptions, with no package initialized, the main
thread only, the Linux file extension's state as on disk (`OsInit`), and a namespace that is
`Safe`: `dir` a directory in which neither `wal.tmp` nor `wal` is a file and, if `wal` is a
directory, its `seg` a file holding the data (`DataGood`): the boot program's result is `#()`, no
thread is stuck and no thread has an unrecovered panic, so `checkDir`'s and `check`'s panics never
fire, however many times the node crashes, in particular whenever a crash interrupts `Create`
(after the removals, the `mkdir`, the create, the write, the sync, the rename of the directory or
the parent's sync). It assumes that the package's initializer runs (`Hinit_wp`). -/
theorem dirswap_crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC osFsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hsafe : Safe dir none (extLocal osFsExt σ.world).ns ∨
      ∃ k, Safe dir (some k) (extLocal osFsExt σ.world).ns ∧
        ∃ fo, (extLocal osFsExt σ.world).files !! k = some fo ∧ DataGood fo)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootDS dir) n ([bootDS dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  dirswap_crash_safety_bounded (GF := osFsGF) Hinit_wp (n + 1) (n + 2) σ g dir Hlctx Hpkgs Hinit
    Hsafe n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

#print axioms dirswap_crash_safety

end osfs_walfs
end EtcdGrove
end Perennial
