/-
The end-to-end result of `examples/osfs/walfs`'s `seglog.go`: the crash adequacy of its boot
program, which initializes the package and runs `Run(dir)`, at the start and after every crash,
over the Linux file extension v2 (`fs_crash_adequacy`).

`seglog.go` claims no property of the segment's contents: the theorem is that every call the
segment's life makes (an OFD lock, `Seek` from the start, the offset and the end, `Write` at the
offset, `fallocate` growing the file and keeping its size, `fdatasync`, a shrinking `Truncate`,
`Read` at the offset, `unlink` and `rmdir`) is one the extension's trusted models cover, so that
their "not modelled" panics never fire and no run is stuck, however often the node crashes
(each crash keeping a set of the logged metadata operations closed under the journal order; a
process restart is a machine crash under the semantics' "Restarts" assumption). There is no crash
invariant: the boot program removes whatever is at `seg.log` and makes a new segment, so it needs
nothing of what a crash left. Each generation starts from the shared view's resources of its durable
tree (`osShared R (m, [])`, `m` well formed), takes the whole claim on `seg.log` from them
(`log_start`), and runs `Run`; after a crash, the next generation's resources come from the old
generation's `osSharedInv` (`crashRest_treeS'`).

**What is assumed**, as for `segdir` (`Results.lean`): the package initializer (`Hinit_wp`), the
hand-written `os.file` field facts, and the Goose-generated package facts of `os` and
`golang.org/x/sys/unix` (`[os.Assumptions]`, `[golang_org.x.sys.unix.Assumptions]`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLog
public import Proof.os.File__WriteAt
public import Proof.os.File__Fd
public import Proof.os.File__Close
public import Proof.syscall.Fdatasync
public import GooseLang.Ext.Fs.Adequacy
public import Robustness.Statement

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

/-- `seglog`'s boot program: initialize the package, then call `Run(dir)`. -/
def bootLog [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Run []))) (Val #())) (Val #dir))

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The precondition of `seglog`'s boot program in the generation `L`, the roots `R`: the shared
view's resources of a well-formed durable tree. -/
def bootPreLog [G : GooseGlobalGS .hasLC GF] (R : Roots) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ m : Tree, osShared (L := L) R (m, []) ∗ ⌜TreeWf R m⌝)

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
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootLog dir) n ([bootLog dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (bootLog dir) T n ([bootLog dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  obtain ⟨j, hrj⟩ := Hdir
  have hR : RootsOk (extLocal fsExt σ.world).fs.roots := Hinit.2.2.2.1
  obtain ⟨R, hRdef⟩ : ∃ R, (extLocal fsExt σ.world).fs.roots = R := ⟨_, rfl⟩
  rw [hRdef] at hR hrj
  refine fs_crash_adequacy (GF := GF) N T (bootLog dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPreLog R L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the tree as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos - Hh Hgs
    rw [hRdef]
    unfold bootPreLog
    imodintro
    iframe Hos Hgs
    iexists _
    iframe Hh
    ipureintro; rw [← hRdef]; exact Hinit.2.2.2.2.1
  · -- every generation: the program's claim, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPreLog
    iintro ⟨#Hos, Hgs, %m, Hsh, %hwf⟩ _
    imod log_start (L := hG.goose_localGS) R hR dir j hrj m hwf ⊤ CoPset.subseteq_top $$ Hsh
      with ⟨#Hsi, Hh, Hsub⟩
    imodintro
    isplitl [Hgs Hh Hsub]
    · -- the boot program
      unfold bootLog
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_Run os.File.Close.wp_proof os.File.WriteAt.wp_proof os.File.Fd.wp_proof
          syscall.Fdatasync.wp_proof R dir j hrj _ $$ [Hh Hsub]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: the next generation's resources from the old generation's `osSharedInv`
      iintro %L' %V' _ #Hos' Hr Hgs' -
      imod crashRest_treeWf' (fun _ _ => True) hG.goose_localGS L' [] false V' R ⊤ CoPset.subseteq_top
        $$ Hsi Hr with ⟨%hwf', Hr⟩
      imod crashRest_treeS' (fun _ _ => True) hG.goose_localGS L' [] V' R ⊤ CoPset.subseteq_top
        $$ Hsi Hr with ⟨%hV, Hsh', -⟩
      obtain ⟨m', l⟩ := V'
      simp only at hV
      subst hV
      have hnow : Hist.now ((m', []) : Hist) = m' := by simp [Hist.now, Hist.ops, replay]
      rw [hnow] at hwf'
      imodintro
      iframe Hos' Hgs'
      iexists m'
      iframe Hsh'
      ipureintro; exact hwf'

/-- **Crash safety of `examples/osfs/walfs`'s `seglog.Run`.** In every execution with crashes of
the boot program (`RealCrashNsteps`, the real semantics), from a state whose Go context satisfies
the Go semantics and the packages' assumptions, with no package initialized, the main thread
only, the Linux file extension's state as on disk (`FsInit`), `dir` one of its roots: the boot
program's result is `#()`, no thread is stuck and no thread has an unrecovered panic, so every
call of the segment's life is one the trusted models cover, however many times the node crashes.
It assumes that the package's initializer runs (`Hinit_wp`). (`seglog_crash_safety_bounded` with
the ghost state `fsGF`.) -/
theorem seglog_crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions] [golang_org.x.sys.unix.Assumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC fsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootLog dir) n ([bootLog dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  seglog_crash_safety_bounded (GF := fsGF) Hinit_wp (n + 1) (n + 2) σ g dir Hlctx Hpkgs Hinit Hdir
    n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

end osfs_walfs
end EtcdGrove
end Perennial

end
