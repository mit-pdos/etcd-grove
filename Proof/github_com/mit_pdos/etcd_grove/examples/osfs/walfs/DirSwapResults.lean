/-
The end-to-end result of `examples/osfs/walfs`'s `dirswap.go`: the crash adequacy of its boot
program, which initializes the package and runs `BootDir(dir)`, at the start and after every
crash, over the Linux file extension v2 (`fs_crash_adequacy`: a crash keeps a set of the logged
metadata operations closed under the journal order, replayed; a process restart is a machine crash
under the semantics' "Restarts" assumption).

The boot program's precondition, over a generation's local ghost state `L` (`bootPreDS`), is `L`'s
invariant of the mapped cells, the shared view's resources of the durable tree `m` the generation
starts from (`osShared R (m, [])`), `m` well formed and `SafeT` (`DSClaims.lean`) with some key `ko`,
and that key's file as `L` starts with it (`startFile`), `DataGood`. Each generation splits the
claims of `m` between its crash invariant (`dsInv`) and the program (`ds_start`) and runs `BootDir`
(`wp_BootDir`). After a crash, the crash part opens the old generation's invariant (`ds_crash`): the
tree left is `SafeT` with the invariant's key, whose file in the new generation is a crash of the
invariant's half, so `DataGood` (if the crash dropped it, the key `none` will do); the next
generation's shared resources come from the old generation's `osSharedInv` (`crashRest_treeS'`).

**What is assumed**, as for `segdir`'s result (`Results.lean`): the package initializer
(`Hinit_wp`), the hand-written `os.file` field facts and `os`'s Goose-generated package facts
(`[os.Assumptions]`) (instance hypotheses).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwap
public import Proof.os.File__ReadAt
public import Proof.os.File__WriteAt
public import Proof.os.File__Close
public import Proof.os.File__Sync
public import GooseLang.Ext.Fs.Adequacy
public import Robustness.Statement

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase DS
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

/-- The boot program: initialize the package, then call `BootDir(dir)`. -/
def bootDS [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve BootDir []))) (Val #())) (Val #dir))

section gen
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- The precondition of the boot program in the generation `L`, the roots `R`, `dir` the root of
`j`. -/
def bootPreDS (R : Roots) (j : Ino) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (m : Tree) (ko : Option Ino), osShared (L := L) R (m, []) ∗
      ⌜TreeWf R m ∧ SafeT j ko m⌝ ∗ startFile (L := L) ko)

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
    (N T : Nat) (σ : state) (g : GlobalState) (dir : GoString) (j : Ino)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hsafe : SafeT j none (extLocal fsExt σ.world).fs.treeDur ∨
      ∃ k, SafeT j (some k) (extLocal fsExt σ.world).fs.treeDur ∧
        ∃ f, (extLocal fsExt σ.world).fs.files !! k = some f ∧ DataGood (some f))
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootDS dir) n ([bootDS dir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (bootDS dir) T n ([bootDS dir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hR : RootsOk (extLocal fsExt σ.world).fs.roots := Hinit.2.2.2.1
  have hdisk : ∀ i f, (extLocal fsExt σ.world).fs.files !! i = some f →
      ∃ vs sz, f = OsFile.ofDisk vs sz := fun i f hf =>
    let ⟨vs, sz, _, e⟩ := (Hinit.2.2.2.2.2.2.1 i f hf).2; ⟨vs, sz, e⟩
  obtain ⟨R, hRdef⟩ : ∃ R, (extLocal fsExt σ.world).fs.roots = R := ⟨_, rfl⟩
  rw [hRdef] at hR Hdir
  refine fs_crash_adequacy (GF := GF) N T (bootDS dir) σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinit (fun L => bootPreDS R j L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the tree and the file as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos Hfs Ht Hgs
    rw [hRdef]
    unfold bootPreDS
    imodintro
    iframe Hos Hgs
    have hwf : TreeWf R (extLocal fsExt σ.world).fs.treeDur := hRdef ▸ Hinit.2.2.2.2.1
    rcases Hsafe with hs | ⟨k, hs, f, hf, hgood⟩
    · iexists _, none
      iframe Ht
      isplitr
      · ipureintro; exact ⟨hwf, hs⟩
      unfold startFile; iempintro
    · icases (BigSepM.bigSepM_lookup
        (Φ := fun i f => osFileStart (L := hG.goose_localGS) i f) hf) $$ Hfs with Hf
      iexists _, (some k)
      iframe Ht
      isplitr
      · ipureintro; exact ⟨hwf, hs⟩
      unfold startFile
      iexists _
      iframe Hf
      ipureintro; exact hgood
  · -- every generation: the invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPreDS
    iintro ⟨#Hos, Hgs, %m, %ko0, Hsh, %hs, Hsf⟩ _
    icases startFile_split (L := hG.goose_localGS) ko0 $$ Hsf with ⟨Hk, Hs⟩
    imod ds_start (L := hG.goose_localGS) R dir j Hdir m hs.1 ko0 hs.2 ⊤ CoPset.subseteq_top
      $$ Hsh Hk with ⟨%γ, #Hinv, Hh, Ht, HT, HK, #Hsi, -, Hperms, -⟩
    icases osCallPerms_root (L := hG.goose_localGS) R dir j hR Hdir $$ Hperms with ⟨Hperm, -⟩
    imodintro
    isplitl [Hgs Hperm Hh Ht HT HK Hs]
    · -- the boot program
      unfold bootDS
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_BootDir os.File.ReadAt.wp_proof os.File.Close.wp_proof os.File.WriteAt.wp_proof
          os.File.Sync.wp_proof R dir j Hdir γ m ko0 hs.2 $$ [Hperm Hh Ht HT HK Hs]
      · iframe; iframe #
      ipureintro; rfl
    · -- after a crash: the tree and the file from the old generation's invariant
      iintro %L' %V' _ #Hos' Hr Hgs' -
      imod ds_crash (fun _ _ => True) hG.goose_localGS L' R j γ V' $$ Hinv Hsi Hr
        with ⟨%ko, %D, %hs', Hsf, Hr⟩
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
      iexists m', ko
      iframe Hsh' Hsf
      ipureintro; exact ⟨hwf', hs'⟩

/-- **Crash safety of `examples/osfs/walfs`'s `dirswap.BootDir`.** In every execution with crashes
of the boot program (`RealCrashNsteps`, the real semantics), from a state whose Go context
satisfies the Go semantics and the package's assumptions, with no package initialized, the main
thread only, the Linux file extension's state as on disk (`FsInit`), `dir` the root of inode `j`
whose tree is `SafeT`: `wal` no file and, if `wal` is a directory, its `seg` a file holding the
data (`DataGood`): the boot program's result is `#()`, no thread is stuck and no thread has an
unrecovered panic, so `checkDir`'s and `check`'s panics never fire, however many times the node
crashes (a machine crash keeping a set of the logged metadata operations closed under the journal
order), in particular whenever a crash interrupts `Create` (after the removals, the `mkdir`, the
create, the write, the sync, the rename of the directory or the parent's sync). It assumes that
the package's initializer runs (`Hinit_wp`). (`dirswap_crash_safety_bounded` with the ghost state
`fsGF`.) -/
theorem dirswap_crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.Assumptions] [os.file.FieldAssumptions]
    (Hinit_wp : ∀ [hG : HeapGS .hasLC fsGF],
      {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); True }})
    (σ : state) (g : GlobalState) (dir : GoString) (j : Ino)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hsafe : SafeT j none (extLocal fsExt σ.world).fs.treeDur ∨
      ∃ k, SafeT j (some k) (extLocal fsExt σ.world).fs.treeDur ∧
        ∃ f, (extLocal fsExt σ.world).fs.files !! k = some f ∧ DataGood (some f))
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootDS dir) n ([bootDS dir], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  dirswap_crash_safety_bounded (GF := fsGF) Hinit_wp (n + 1) (n + 2) σ g dir j Hlctx Hpkgs Hinit
    Hdir Hsafe n κs t2 σ2 b Hsteps (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

#print axioms dirswap_crash_safety

end osfs_walfs
end EtcdGrove
end Perennial

end
