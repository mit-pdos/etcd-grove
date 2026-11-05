/-
The end-to-end result of `examples/osfs/walfs`'s `seglog.go`: the crash adequacy of its boot
program, which initializes the package and runs `Run(dir)`, at the start and after every crash,
over the Linux file extension with the namespace (`osFs_crash_adequacyN`).

`seglog.go` claims no property of the segment's contents: the theorem is that every call the
segment's life makes (an OFD lock, `Seek` from the start, the offset and the end, `Write` at the
offset, `fallocate` growing the file and keeping its size, `fdatasync`, a shrinking `Truncate`,
`Read` at the offset) is one the extension's trusted models cover, so that their "not modelled"
panics never fire and no run is stuck, however often the node crashes. The crash invariant is
`SegLogOps.lean`'s `logInv`: no crash outcome of `dir` has a directory at `seg.log` (the boot
program removes a leftover segment and makes a new one, so it needs nothing of its contents).

**What is assumed**, as for `segdir` (`Results.lean`): the package initializer (`Hinit_wp`) and
the hand-written `os.file` field facts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLog
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

/-- `seglog`'s boot program: initialize the package, then call `Run(dir)`. -/
def bootLog [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Run []))) (Val #())) (Val #dir))

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The precondition of `seglog`'s boot program in the generation `L`. -/
def bootPreLog [G : GooseGlobalGS .hasLC GF] (dir : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ osNsBusy (L := L) false ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ g : DirG, osDir (L := L) dir (DFrac.own 1) g ∗ ⌜g.pend = [] ∧ NoDirL g⌝)

/-- `seglog_crash_safety` for executions of fewer than `N` steps along which fewer than `T`
threads are live. -/
theorem seglog_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [os.Assumptions] [os.file.FieldAssumptions]
    [golang_org.x.sys.unix.Assumptions] [hPre : GooseGpreS GF]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC GF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (N T : Nat) (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hdir : (extLocal osFsExt σ.world).ns !! dir = some .dir)
    (Hnd : (extLocal osFsExt σ.world).ns !! child dir logB ≠ some .dir)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootLog dir) n ([bootLog dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (bootLog dir) T n ([bootLog dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine osFs_crash_adequacyN (GF := GF) N T (bootLog dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPreLog dir L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the directory as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos - Hds Hz Hgs
    have hdm : dirMap (extLocal osFsExt σ.world) !! dir =
        some ⟨entsOf (extLocal osFsExt σ.world).ns dir, []⟩ := by
      rw [dirMap_lookup, if_pos Hdir]
    icases (BigSepM.bigSepM_lookup
      (Φ := fun d g => osDir (L := hG.goose_localGS) d (DFrac.own 1) g) hdm) $$ Hds with Hd
    unfold bootPreLog
    imodintro
    iframe Hos Hz Hgs
    iexists _
    iframe Hd
    ipureintro
    refine ⟨rfl, fun e he => ?_⟩
    rw [crashTo_nil rfl he]
    show entsOf _ dir !! logB ≠ _
    rw [entsOf_child _ _ _ logB_ok]; exact Hnd
  · -- every generation: the invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPreLog
    iintro ⟨#Hos, Hz, Hgs, %g0, Hd, %hp⟩ _
    icases (osDir_halves (L := hG.goose_localGS) dir g0).1 $$ Hd with ⟨Hd1, Hd2⟩
    imod inv_alloc logN ⊤ (iprop(∃ g : DirG,
        osDir (L := hG.goose_localGS) dir (DFrac.own (1 : Qp).half) g ∗ ⌜NoDirL g⌝)) $$ [Hd2]
      with #Hinv
    · inext; iexists g0; iframe; ipureintro; exact hp.2
    imodintro
    isplitl [Hgs Hd1 Hz]
    · -- the boot program
      unfold bootLog
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_Run os.File.ReadAt.wp_proof os.File.Close.wp_proof os.File.WriteAt.wp_proof
          os.File.Fd.wp_proof syscall.Fdatasync.wp_proof dir g0 hp.1 hp.2 $$ [Hd1 Hz]
      · iframe; iframe #; unfold logInv; iexact Hinv
      ipureintro; rfl
    · -- after a crash: the directory from the old generation's invariant
      iintro %L' _ #Hos' - Hn Hz' Hgs'
      imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%g, >Hd, >%Hp⟩
      icases osNsCrash_take hG.goose_localGS L' [] dir List.not_mem_nil _ g $$ Hn Hd
        with ⟨%g', %hg', Hd', -, Hd⟩
      obtain ⟨hpend, hcr⟩ := hg'
      imod Hclose $$ [Hd] with -
      · inext; iexists g; iframe; ipureintro; exact Hp
      imodintro
      try unfold bootPreLog
      iframe Hos' Hz' Hgs'
      iexists g'
      iframe Hd'
      ipureintro
      exact ⟨hpend, fun e he => by rw [crashTo_nil hpend he]; exact Hp _ hcr⟩

/-- **Crash safety of `examples/osfs/walfs`'s `seglog.Run`.** In every execution with crashes of
the boot program (`RealCrashNsteps`, the real semantics), from a state whose Go context satisfies
the Go semantics and the packages' assumptions, with no package initialized, the main thread
only, the Linux file extension's state as on disk (`OsInit`), `dir` a directory of the
namespace with no directory at `seg.log`: the boot program's result is `#()`, no thread is stuck
and no thread has an unrecovered panic, so every call of the segment's life is one the trusted
models cover, however many times the node crashes. It assumes that the package's initializer
runs (`Hinit_wp`). (`seglog_crash_safety_bounded` with the ghost state `osFsGF`.) -/
theorem seglog_crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions] [golang_org.x.sys.unix.Assumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC osFsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hdir : (extLocal osFsExt σ.world).ns !! dir = some .dir)
    (Hnd : (extLocal osFsExt σ.world).ns !! child dir logB ≠ some .dir)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootLog dir) n ([bootLog dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  seglog_crash_safety_bounded (GF := osFsGF) Hinit_wp (n + 1) (n + 2) σ g dir Hlctx Hpkgs Hinit Hdir
    Hnd n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

end osfs_walfs
end EtcdGrove
end Perennial
