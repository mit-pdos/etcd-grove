/-
The end-to-end result of `examples/osfs/walfs`'s `segdir.go`: the crash adequacy of its boot
program, which initializes the package and runs `Boot(dir)`, at the start and after every crash
(of the machine; a restart of the process alone counts only under the semantics' "Restarts"
assumption, a `sync(2)` before it), over the Linux file extension v2 (`fs_crash_adequacy`: a crash
keeps a set of the logged metadata operations closed under the journal order, replayed).

The boot program's precondition, over a generation's local ghost state `L` (`bootPre`), is `L`'s
invariant of the mapped cells, the shared view's resources of the durable tree `m` the generation
starts from (`osShared R (m, [])`), `m` well formed and `SafeT` (`BootClaims.lean`: no directory at
`dir/seg` or `dir/seg.tmp`, and at `seg` nothing or the file of a key `ko`), and that key's file as
`L` starts with it (`DS.startFile`), `DataGood`. Each generation splits the claim on `seg` and
`seg.tmp` between its crash invariant (`bootInv`) and the program (`boot_start`) and runs `Boot`
(`Boot.lean`'s `wp_Boot`). After a crash, the crash part opens the old generation's invariant
(`boot_crash`): the tree left is `SafeT` with the invariant's key, whose file in the new generation
is a crash of the invariant's half, so `DataGood` (if the crash dropped it, the key `none` will do);
the next generation's shared resources come from the old generation's `osSharedInv`
(`crashRest_treeS'`).

**What is assumed**, as for `examples/osfs/crashlog`: the package initializer (`Hinit_wp`, which
needs `wp_initialize'` of this repository's `os` and `syscall`), the hand-written `os.file` field
facts, and the Goose-generated package facts of the packages it calls (`[os.Assumptions]`, as
`package_sem` is the program's own) (instance hypotheses). The trust base is otherwise the extension's semantics
(`GooseLang/Ext/Fs/Impl.lean`) and the trusted models of `os` and `syscall`
(`TrustedCode/os.lean`, `TrustedCode/syscall.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot
public import Proof.os.File__ReadAt
public import Proof.os.File__SyncS
public import Proof.os.File__WriteAt
public import Proof.os.File__Fd
public import Proof.os.File__Close
public import Proof.syscall.Fdatasync
public import GooseLang.Ext.Fs.Adequacy
public import Robustness.Statement
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs BC
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section gen
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- The precondition of the boot program in the generation `L`, `dir` the root `R`'s directory
`j`. -/
def bootPre (R : Roots) (j : Ino) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (m : Tree) (ko : Option Ino), osShared (L := L) R (m, []) ∗
      ⌜TreeWf R m ∧ SafeT j ko m⌝ ∗ DS.startFile (L := L) ko)

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
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnd : (∀ J, (extLocal fsExt σ.world).lookup (child dir segB) ≠ some (.dir J)) ∧
      (∀ J, (extLocal fsExt σ.world).lookup (child dir tmpB) ≠ some (.dir J)))
    (Hseg : ∀ k, (extLocal fsExt σ.world).lookup (child dir segB) = some (.file k) →
      DataGood ((extLocal fsExt σ.world).fs.files !! k))
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (boot dir) T n ([boot dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  obtain ⟨j, hrj⟩ := Hdir
  have hR : RootsOk (extLocal fsExt σ.world).fs.roots := Hinit.2.2.2.1
  have hlk : ∀ b, NameOk b → (extLocal fsExt σ.world).lookup (child dir b) =
      (extLocal fsExt σ.world).fs.treeDur.entry j b := by
    intro b hb
    rw [lookupH_eq, Hinit.2.1]
    exact DSBase.lookupH_child_root hR hrj _ hb
  rw [hlk segB segB_ok, hlk tmpB tmpB_ok] at Hnd
  rw [hlk segB segB_ok] at Hseg
  obtain ⟨R, hRdef⟩ : ∃ R, (extLocal fsExt σ.world).fs.roots = R := ⟨_, rfl⟩
  rw [hRdef] at hR hrj
  obtain ⟨m0, hm0⟩ : ∃ m0, (extLocal fsExt σ.world).fs.treeDur = m0 := ⟨_, rfl⟩
  rw [hm0] at Hnd Hseg
  -- the key the first generation starts with: the file `seg` names, if any
  obtain ⟨ko0, hso⟩ : ∃ ko0, SafeT j ko0 m0 ∧
      ∀ k, ko0 = some k → m0.entry j segB = some (.file k) := by
    cases hs : m0.entry j segB with
    | none => exact ⟨none, ⟨Hnd.1, Hnd.2, .inl hs⟩, fun _ h => by cases h⟩
    | some x =>
      cases x with
      | dir J => exact absurd hs (Hnd.1 J)
      | file k => exact ⟨some k, ⟨Hnd.1, Hnd.2, .inr ⟨k, rfl, hs⟩⟩, fun _ h => by cases h; rfl⟩
  have hwf : TreeWf R m0 := by rw [← hRdef, ← hm0]; exact Hinit.2.2.2.2.1
  refine fs_crash_adequacy (GF := GF) N T (boot dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPre R j L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the tree and the files as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Ht Hgs
    rw [hRdef, hm0]
    unfold bootPre
    imodintro
    iframe Hos Hgs
    iexists m0, ko0
    iframe Ht
    isplitr
    · ipureintro; exact ⟨hwf, hso.1⟩
    cases ko0 with
    | none => unfold DS.startFile; iempintro
    | some k =>
      have hk := hso.2 k rfl
      have hnm : Named (extLocal fsExt σ.world).fs.treeDur k := ⟨j, segB, by rw [hm0]; exact hk⟩
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (Hinit.2.2.2.2.2.1 k hnm)
      have hgood : DataGood (some f) := by rw [← hf]; exact Hseg k hk
      icases (BigSepM.bigSepM_lookup
        (Φ := fun i f => osFileStart (L := hG.goose_localGS) i f) hf) $$ Hfs with Hf
      unfold DS.startFile
      iexists f
      iframe Hf
      ipureintro; exact hgood
  · -- every generation: the invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPre
    iintro ⟨#Hos, Hgs, %m, %ko, Hsh, %hs, Hsf⟩ _
    icases DS.startFile_split (L := hG.goose_localGS) ko $$ Hsf with ⟨Hk, Hs⟩
    imod boot_start (L := hG.goose_localGS) R dir j hrj m hs.1 ko hs.2 ⊤ CoPset.subseteq_top
      $$ Hsh Hk with ⟨%γ, #Hinv, Hh, #Hsi, Hperms⟩
    icases osCallPerms_root (L := hG.goose_localGS) R dir j hR hrj $$ Hperms with ⟨Hperm, -⟩
    imodintro
    isplitl [Hgs Hperm Hh Hs]
    · -- the boot program
      unfold boot
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_Boot os.File.Sync.wp_proofDirS os.File.ReadAt.wp_proof os.File.Close.wp_proof os.File.WriteAt.wp_proof
          os.File.Fd.wp_proof syscall.Fdatasync.wp_proof R dir j hrj γ ko _ $$ [Hperm Hh Hs]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: the tree and the file from the old generation's invariant
      iintro %L' %V' _ #Hos' Hr Hgs' -
      imod boot_crash (fun _ _ => True) hG.goose_localGS L' R j γ V' $$ Hinv Hsi Hr
        with ⟨%ko', %D, %hs', Hsf, Hr⟩
      imod crashRest_treeWf' (fun _ _ => True) hG.goose_localGS L' D false V' R ⊤ CoPset.subseteq_top
        $$ Hsi Hr with ⟨%hwf', Hr⟩
      imod crashRest_treeS' (fun _ _ => True) hG.goose_localGS L' D V' R ⊤ CoPset.subseteq_top
        $$ Hsi Hr with ⟨%hV, Hsh', -⟩
      obtain ⟨m', l⟩ := V'
      simp only at hV
      subst hV
      have hnow : Hist.now ((m', []) : Hist) = m' := by simp [Hist.now, Hist.ops, replay]
      rw [hnow] at hs' hwf'
      imodintro
      iframe Hos' Hgs'
      iexists m', ko'
      iframe Hsh' Hsf
      ipureintro; exact ⟨hwf', hs'⟩

/-- **Crash safety of `examples/osfs/walfs`'s `segdir.Boot`.** In every execution with crashes of
the boot program (`RealCrashNsteps`, the real semantics; a crash of the machine, a restart of the
process alone being one under the semantics' "Restarts" assumption), from a state whose Go context satisfies the Go semantics and the package's assumptions,
with no package initialized, the main thread only, the Linux file extension's state as on disk
(`FsInit`), `dir` one of its roots, in which neither `dir/seg` nor `dir/seg.tmp` is a directory and
`dir/seg`, if it names a file, names one that is `DataGood` (the 8 bytes of data at 0): the
boot program's result is `#()`, no thread is stuck and no thread has an unrecovered panic, so
`check`'s panic never fires, however many times the node crashes or (after a `sync`) the process restarts, and in
particular whenever one interrupts `commit` (after the create, the write, the `fdatasync`, the
rename or the directory's sync). It assumes that the package's initializer runs (`Hinit_wp`, the
module docstring). (`crash_safety_bounded` with the ghost state `fsGF`.) -/
theorem crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC fsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnd : (∀ J, (extLocal fsExt σ.world).lookup (child dir segB) ≠ some (.dir J)) ∧
      (∀ J, (extLocal fsExt σ.world).lookup (child dir tmpB) ≠ some (.dir J)))
    (Hseg : ∀ k, (extLocal fsExt σ.world).lookup (child dir segB) = some (.file k) →
      DataGood ((extLocal fsExt σ.world).fs.files !! k))
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  crash_safety_bounded (GF := fsGF) Hinit_wp (n + 1) (n + 2) σ g dir Hlctx Hpkgs Hinit Hdir Hnd
    Hseg n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

#print axioms crash_safety

end osfs_walfs
end EtcdGrove
end Perennial

end
