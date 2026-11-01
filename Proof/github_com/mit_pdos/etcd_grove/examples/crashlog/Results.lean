/-
The end-to-end result of `examples/crashlog`: the crash adequacy of its boot program, which
initializes the package and runs `Boot(dir)`, at the start and after every crash, over the Linux
file extension (`osFs_crash_adequacyT`, the crash interpretation that keeps the changes in
flight).

The boot program's precondition, over a generation's local ghost state `L`, is `L`'s invariant of
the mapped cells, the file at `dir/log` as `L` starts with it (`osFileStart`), `Good` (the crash
invariant: a nonzero flag means the data), and the package state of a fresh program. Each
generation puts the file in its crash invariant (`cfInv_alloc`) and runs `Boot`
(`Boot.lean`'s `wp_Boot`); after a crash, the crash part opens the old generation's invariant and
takes the file from it (`cfInv_crash_keep`), a `Good` file of the new generation.

**What is assumed.** The package initializer is not proved: `crash_safety` takes as a hypothesis
`Hinit_wp`, that the package's `initialize'` runs from the fresh package state (`ownGoState ∅`)
without getting stuck or panicking. Proving it needs `wp_initialize'` of this repository's `os`,
`syscall` (and their imports' `io/fs`, Perennial's `io` and `errors`): `etc/gen-init.py` does not
generate them (its roots do not reach project bboltfs's translations, whose `os` initializer runs
`init.0` and allocates about thirty variables, `Stdin`, `ErrNotExist`, ..., many of them
untranslated initializers that would need its trust-boundary axioms). `Boot` itself reads no
package variable, so nothing of the initialized state is needed beyond that.
The hand-written `os.file` and `os.fileStat` field facts (`TrustedCode/os.lean`) are instance
hypotheses, as for every `OpenFile` and `Stat` spec.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.crashlog.Boot
public import Proof.os.Crash
public import Proof.os.File__ReadAt
public import Proof.os.File__Stat
public import Proof.os.fileStat__Size
public import Proof.os.File__Fd
public import Proof.os.File__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.crashlog

attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs
  osFsExtsCrashInterpT

/-- The boot program: initialize the package, then call `Boot(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Boot []))) (Val #())) (Val #dir))

/-- A generation's file starts `Good`: a crash before it is opened leaves it as it is. -/
theorem crash_start (fo : Option OsFile) (hg : Good fo) : CrashOk Good (startState fo) := by
  cases fo with
  | none => intro fo' h; cases h; trivial
  | some f => exact crash_open (some f) hg

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The precondition of the boot program in the generation `L`. -/
def bootPre [G : GooseGlobalGS .hasLC GF] (dir : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ (∃ fo, ⌜Good fo⌝ ∗ osFileStart (L := L) (dir ++ go!"/log") fo) ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

/-- `crash_safety` for executions of fewer than `N` steps along which fewer than `T` threads are
live. -/
theorem crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    [hPre : GooseGpreS GF]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC GF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (N T : Nat) (σ : state) (g : GlobalState) (dir : GoString) (fo : Option OsFile)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hfile : (extLocal osFsExt σ.world).files !! (dir ++ go!"/log") = some fo) (Hgood : Good fo)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (boot dir) T n ([boot dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine osFs_crash_adequacyT (GF := GF) N T (boot dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPre dir L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the file as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Hgs
    icases (BigSepM.bigSepM_lookup (Φ := fun p fo => osFileStart (L := hG.goose_localGS) p fo)
      Hfile) $$ Hfs with Hf
    imodintro
    unfold bootPre
    iframe Hos Hgs
    iexists fo
    iframe Hf
    ipureintro; exact Hgood
  · -- every generation: the file in its invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPre
    iintro ⟨#Hos, ⟨%fo0, %hg0, Hf⟩, Hgs⟩ _
    imod cfInv_alloc (L := hG.goose_localGS) logN (dir ++ go!"/log") Good fo0 (crash_start fo0 hg0)
      $$ Hf with ⟨%γ, #Hinv, Hown⟩
    imodintro
    isplitl [Hgs Hown]
    · -- the boot program
      unfold boot
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_Boot os.OpenFile.wp_proof_crash os.File.Close.wp_proof os.File.ReadAt.wp_proof
          os.File.WriteAt.wp_proof_crash os.File.Fd.wp_proof syscall.Fdatasync.wp_proof_crash
          os.File.Stat.wp_proof os.fileStat.Size.wp_proof dir γ fo0 hg0 $$ [Hown]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: take the file from the old generation's invariant
      iintro %L' _ #Hos' Hr Hgs'
      unfold cfInv
      imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%s, >Hv, >Hs, >%Hok⟩
      icases cfInv_crash_keep hG.goose_localGS L' [] (dir ++ go!"/log") List.not_mem_nil Good s Hok
        $$ Hr Hs with ⟨%fo', %hg', Hf', -, Hs⟩
      imod Hclose $$ [Hv Hs] with -
      · inext; iexists s; iframe; ipureintro; exact Hok
      imodintro
      iframe Hos' Hgs'
      iexists fo'
      iframe Hf'
      ipureintro; exact hg'

/-- **Crash safety of `examples/crashlog`.** In every execution with crashes of the boot program
(`RealCrashNsteps`, the real semantics), from a state whose Go context satisfies the Go semantics
and the package's assumptions, with no package initialized, the main thread only, the Linux file
extension's state as on disk (`OsInit`) and the file at `dir/log` absent or `Good` (a nonzero
flag byte at offset 8 means the 8 bytes of data at offset 0, and the size below `2^62`): the boot
program's result is `#()`, no thread is stuck and no thread has an unrecovered panic, so `Boot`'s
panics never fire, however many times the node crashes. It assumes that the package's initializer
runs (`Hinit_wp`, the module docstring). (`crash_safety_bounded` with the ghost state `osFsGF`.) -/
theorem crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC osFsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString) (fo : Option OsFile)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hfile : (extLocal osFsExt σ.world).files !! (dir ++ go!"/log") = some fo) (Hgood : Good fo)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  crash_safety_bounded (GF := osFsGF) Hinit_wp (n + 1) (n + 2) σ g dir fo Hlctx Hpkgs Hinit Hfile
    Hgood n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

#print axioms crash_safety

end crashlog
end EtcdGrove
end Perennial
