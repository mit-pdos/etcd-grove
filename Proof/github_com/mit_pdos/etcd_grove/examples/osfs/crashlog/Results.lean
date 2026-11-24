/-
The end-to-end result of `examples/osfs/crashlog`: the crash adequacy of its boot program, which
initializes the package and runs `Boot(dir)`, at the start and after every crash, over the Linux
file extension v2 (`fs_crash_adequacy`).

The boot program's precondition, over a generation's local ghost state `L` (`bootPre`), is `L`'s
invariant of the mapped cells, the tree's start resources (`osShared`) on a well-formed tree with
nothing logged (`(m, [])`), the file at `dir/log` as `L` starts with it (`startAt`: nothing, or the
file `dir/log` names, on disk; never a directory), `Good` (the crash invariant: a nonzero flag means
the data), and the package state of a fresh program. Each generation takes the claim on `log` from
its start resources (`osShared_file`), puts the file and half of the claim in its crash invariant
(`cfInv_alloc`) and runs `Boot` (`Boot.lean`'s `wp_Boot`); after a crash, the crash part opens the
old generation's invariant and takes from it what the crash left at `dir/log` (`cfInv_crash_keep`,
over `crashRest_region'`): a `Good` file, or none; the new generation's tree resources come from the
restart (`crashRest_treeS'`).

**The package initializer** is proved (2026-11-24; until then the hypothesis `Hinit_wp`, that it runs
from the fresh package state): each generation turns its fresh package state into the right to
initialize (`ownInitializing_of_empty`) and runs the generated `wp_initialize'` (`Init.lean`, over the
program's package table `PkgTable.lean`), whose `isPkgInit` `Boot` takes (the path specs of `os` take
`os`'s).
The hand-written `os.file` and `os.fileStat` field facts (`TrustedCode/os.lean`) are instance
hypotheses, as for every `OpenFile` and `Stat` spec.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.Boot
public import Proof.os.Crash
public import Proof.os.File__ReadAt
public import Proof.os.File__Stat
public import Proof.os.fileStat__Size
public import Proof.os.File__Fd
public import Proof.os.File__Close
public import GooseLang.Ext.Fs.Adequacy
public import Robustness.Statement
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.PkgTable
public import Proof.runtime.InitEmpty

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.crashlog
open Fs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section start
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- **A generation's file starts `Good`**: what `startAt` gives of a history with nothing logged,
with the generation's claim on the file's name (`namesOf`), is the start of an idle state
(`StartOk`) whose every crash is `Good`, as `cfInv_alloc` takes it. -/
theorem startAt_start [L : GooseLocalGS GF] (p : GoString) (R : Roots) (m : Tree) (j : Ino)
    (b : GoString) (hfa : FileAt R p j b) (fo : Option OsFile) (hg : Good fo) :
    startAt L p R (m, []) fo ⊢ ∃ s, ⌜StartOk s ∧ CrashOk Good j b s (namesOf (m, []) j (.only [b])) ∧
      CfWf s ∧ PathOk b s (namesOf (m, []) j (.only [b])) ∧ ∀ i m bs x, s ≠ some (i, m, bs, some x)⌝ ∗
      startRes (L := L) s := by
  have hcur := namesOf_cur (m, []) j b
  rw [← lookupH_fileAt hfa] at hcur
  unfold startAt
  cases hl : lookupH R (m, []) p with
  | none =>
    iintro %hfo
    subst hfo
    iexists none
    isplitr
    · ipureintro
      have hp : PathOk b none (namesOf (m, []) j (.only [b])) := by
        show _ = none; rw [hcur, hl]
      refine ⟨.inl rfl, ⟨treeOk_init rfl hp (fun _ => trivial), fun i x h => by cases h⟩, trivial,
        hp, fun _ _ _ _ h => by cases h⟩
    · unfold startRes; iempintro
  | some x =>
    cases x with
    | dir J => iintro %h; exact h.elim
    | file i =>
      iintro ⟨%f, %hfo, Hf⟩
      subst hfo
      iexists some (i, initMeta f, f.contents.map durB, none)
      isplitr
      · ipureintro
        have hp : PathOk b (some (i, initMeta f, f.contents.map durB, none))
            (namesOf (m, []) j (.only [b])) := by
          show _ = _; rw [hcur, hl]
        refine ⟨.inr ⟨i, f, rfl, hg⟩, ⟨treeOk_init rfl hp (fun h => by
            rw [← lookupH_fileAt hfa] at h; rw [hl] at h; cases h), fun i' x h => ?_⟩, ⟨?_, rfl⟩,
          hp, fun _ _ _ _ h => by cases h⟩
        · cases h; exact crash_start f hg
        · rw [List.length_map, contents_length]; rfl
      · unfold startRes osFileStart; iexact Hf

end start

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The precondition of the boot program in the generation `L`, `R` the roots: the generation's
start resources on a well-formed tree `m` with nothing logged, and the file at `dir/log`. -/
def bootPre [G : GooseGlobalGS .hasLC GF] (R : Roots) (dir : GoString) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (m : Tree) (fo : Option OsFile), osShared (L := L) R (m, []) ∗ ⌜TreeWf R m ∧ Good fo⌝ ∗
      startAt L (child dir logB) R (m, []) fo)

/-- `crash_safety` for executions of fewer than `N` steps along which fewer than `T` threads are
live. -/
theorem crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    [hPre : GooseGpreS GF]
    (N T : Nat) (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnd : ∀ J, (extLocal fsExt σ.world).lookup (child dir logB) ≠ some (.dir J))
    (Hlog : ∀ k, (extLocal fsExt σ.world).lookup (child dir logB) = some (.file k) →
      Good ((extLocal fsExt σ.world).fs.files !! k))
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (boot dir) T n ([boot dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  obtain ⟨j, hrj⟩ := Hdir
  have hR : RootsOk (extLocal fsExt σ.world).fs.roots := Hinit.2.2.2.1
  have hl0 : (extLocal fsExt σ.world).lookup (child dir logB) =
      lookupH (extLocal fsExt σ.world).fs.roots ((extLocal fsExt σ.world).fs.treeDur, [])
        (child dir logB) := by
    rw [lookupH_eq, Hinit.2.1]
  rw [hl0] at Hnd Hlog
  obtain ⟨R, hRdef⟩ : ∃ R, (extLocal fsExt σ.world).fs.roots = R := ⟨_, rfl⟩
  rw [hRdef] at hR hrj Hnd Hlog
  obtain ⟨m0, hm0⟩ : ∃ m0, (extLocal fsExt σ.world).fs.treeDur = m0 := ⟨_, rfl⟩
  rw [hm0] at Hnd Hlog
  have hfa : FileAt R (child dir logB) j logB := ⟨hR, logB_ok, dir, hrj, rfl⟩
  refine fs_crash_adequacy (GF := GF) N T (boot dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPre R dir L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the tree and the file as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Ht Hgs
    rw [hRdef, hm0]
    unfold bootPre
    imodintro
    iframe Hos Hgs
    have hw : TreeWf R m0 := by rw [← hRdef, ← hm0]; exact Hinit.2.2.2.2.1
    cases hlk : lookupH R (m0, []) (child dir logB) with
    | none =>
      iexists m0, none
      iframe Ht
      isplitr
      · ipureintro; exact ⟨hw, trivial⟩
      unfold startAt; rw [hlk]; ipureintro; rfl
    | some x =>
      cases x with
      | dir J => exact absurd hlk (Hnd J)
      | file k =>
        have hnm : Named (extLocal fsExt σ.world).fs.treeDur k := by
          rw [hm0]; exact named_of_lookup hlk
        obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (Hinit.2.2.2.2.2.1 k hnm)
        have hgood : Good (some f) := by rw [← hf]; exact Hlog k hlk
        icases (BigSepM.bigSepM_lookup
          (Φ := fun i f => osFileStart (L := hG.goose_localGS) i f) hf) $$ Hfs with Hf
        iexists m0, (some f)
        iframe Ht
        isplitr
        · ipureintro; exact ⟨hw, hgood⟩
        unfold startAt; rw [hlk]
        iexists f
        iframe Hf
        ipureintro; rfl
  · -- every generation: the file in its invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPre
    iintro ⟨#Hos, Hgs, %m, %fo, Hsh, %hg, Hst⟩ _
    obtain ⟨hw, hg⟩ := hg
    imod osShared_file (L := hG.goose_localGS) R (m, []) dir j logB ⊤ CoPset.subseteq_top hR hrj hw
      $$ Hsh with ⟨#Hsi, Hperm, Hn⟩
    icases startAt_start (L := hG.goose_localGS) (child dir logB) R m j logB hfa fo hg $$ Hst
      with ⟨%s, %hso, Hsr⟩
    obtain ⟨hst, hok, hwf, hp, hs⟩ := hso
    imod cfInv_alloc (L := hG.goose_localGS) logN (child dir logB) R j logB _ Good s hs hfa hok hwf hp
      $$ Hn Hsr with ⟨%γ, #Hinv, Hown⟩
    imodintro
    isplitl [Hgs Hperm Hown]
    · -- the boot program
      unfold boot
      ihave Hown0 := ownInitializing_of_empty
        (github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.getIsPkgInit (GF := GF)) $$ Hgs
      wp_apply (github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.wp_initialize' _
        github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.getIsPkgInit_wf) $$ Hown0 as ⟨-, #Hpkg⟩
      wp_pures
      wp_apply wp_Boot os.OpenFile.wp_proof_crash os.File.Close.wp_proof os.File.ReadAt.wp_proof
          os.File.WriteAt.wp_proof_crash os.File.Fd.wp_proof syscall.Fdatasync.wp_proof_crash
          os.File.Stat.wp_proof os.fileStat.Size.wp_proof dir R 1 γ s hst $$ [Hperm Hown]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: the file from the old generation's invariant, the tree from the restart
      iintro %L' %V' _ #Hos' Hr Hgs' -
      unfold cfInv
      imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%s', %j', %b', %W, >%hfa', >Hv, >Hs, >Hn, >%Hok⟩
      imod cfInv_crash_keep (fun _ _ => True) hG.goose_localGS L' [] false V' (child dir logB) R
          Good s' j' b' W _ logN_disjS hfa' (fun _ _ => List.not_mem_nil) Hok $$ Hsi Hr Hs Hn
        with ⟨%fo', %hfo', Hst, ⟨%D', Hr⟩, Hs, Hn⟩
      imod Hclose $$ [Hv Hs Hn] with -
      · inext; iexists s', j', b', W; iframe; isplitr
        · ipureintro; exact hfa'
        ipureintro; exact Hok
      imod crashRest_treeWf' (fun _ _ => True) hG.goose_localGS L' D' false V' R ⊤
        CoPset.subseteq_top $$ Hsi Hr with ⟨%hw', Hr⟩
      imod crashRest_treeS' (fun _ _ => True) hG.goose_localGS L' D' V' R ⊤ CoPset.subseteq_top
        $$ Hsi Hr with ⟨%hV', Hsh, -⟩
      imodintro
      iframe Hos' Hgs'
      rcases V' with ⟨m', l'⟩
      simp only at hV'
      subst hV'
      iexists m', fo'
      iframe Hsh Hst
      ipureintro; exact ⟨hw', hfo'⟩

/-- **Crash safety of `examples/osfs/crashlog`.** In every execution with crashes of the boot program
(`RealCrashNsteps`, the real semantics), from a state whose Go context satisfies the Go semantics
and the package's assumptions, with no package initialized, the main thread only, the Linux file
extension's state as on disk (`FsInit`), `dir` one of its roots, in which `dir/log` is not a
directory and, if it names a file, names one that is `Good` (a nonzero flag byte at offset 8 means
the 8 bytes of data at offset 0, and the size below `2^62`): the boot program's result is `#()`, no
thread is stuck and no thread has an unrecovered panic, so `Boot`'s panics never fire, however many
times the node crashes. (`crash_safety_bounded` with the ghost state `fsGF`.) -/
theorem crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnd : ∀ J, (extLocal fsExt σ.world).lookup (child dir logB) ≠ some (.dir J))
    (Hlog : ∀ k, (extLocal fsExt σ.world).lookup (child dir logB) = some (.file k) →
      Good ((extLocal fsExt σ.world).fs.files !! k))
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  crash_safety_bounded (GF := fsGF) (n + 1) (n + 2) σ g dir Hlctx Hpkgs Hinit Hdir Hnd
    Hlog n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

#print axioms crash_safety

end osfs_crashlog
end EtcdGrove
end Perennial

end
