/-
The end-to-end result of `examples/osfs/walfs`'s `segdir.go`: the crash adequacy of its boot
program, which initializes the package and runs `Boot(dir)`, at the start and after every crash
(of the machine; a restart of the process alone counts only under the semantics' "Restarts"
assumption, a `sync(2)` before it), over the Linux file extension v2 (`fs_crash_adequacy`).

The boot program's precondition, over a generation's local ghost state `L` (`bootPre`), is `L`'s
invariant of the mapped cells, the whole of the tree's history `V`, whose every crash has no
directory at `dir/seg` or `dir/seg.tmp` and at `seg` nothing or the file of a key `ko` (`SafeH`),
and in none of which `seg` is there unless it is there now (`MonoH`), and, for the key, the file
as `L` starts with it (`osFileStartO`), `DataGood` (absent, or the data at 0, clean), there if
`seg` names it now. Each generation puts half of the history and of the first 8 bytes of the file
in its crash invariant (`bootInv`) and runs `Boot` (`Boot.lean`'s `wp_Boot`). After a crash, the
crash part opens the old generation's invariant: the new history is a crash of the old one
(`osTreeCrash_take`: the same after a restart, a prefix of the logged operations replayed after a
machine crash), so `SafeH` and `MonoH` hold of it; the key's file in the new generation is a crash
of the invariant's half (`osCrash_take_runs_keep`), so `DataGood`, and there if a name names it.

**What is assumed**, as for `examples/osfs/crashlog`: the package initializer (`Hinit_wp`, which
needs `wp_initialize'` of this repository's `os` and `syscall`), and the hand-written `os.file`
field facts (instance hypotheses). The trust base is otherwise the extension's semantics
(`GooseLang/Ext/Fs/Impl.lean`) and the trusted models of `os` and `syscall`
(`TrustedCode/os.lean`, `TrustedCode/syscall.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot
public import Proof.os.File__ReadAt
public import Proof.os.File__WriteAt
public import Proof.os.File__Fd
public import Proof.os.File__Close
public import Proof.syscall.Fdatasync
public import GooseLang.Ext.Fs.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

/-- The boot program: initialize the package, then call `Boot(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Boot []))) (Val #())) (Val #dir))

/-! ## The file of the key as a generation starts with it -/

theorem durs_take8 (f : OsFile) (h8 : 8 ≤ f.size) {b : Nat} (hb : b < 8) :
    ((f.contents.map durB).take 8)[b]? = some (durB (f.cache b)) := by
  rw [List.getElem?_take_of_lt hb, List.getElem?_map, contents_getElem?_of_lt (by omega)]; rfl

/-- The invariant's half of a `DataGood` file a generation starts with: every crash of it is
`DataGood` (its first 8 bytes are durable). -/
theorem start_key (f : OsFile) (hg : DataGood (some f)) :
    ∀ fo, FileCrashedR (initMeta f) [(0, DFrac.own (1 : Qp).half, (f.contents.map durB).take 8)] fo →
      DataGood fo := by
  obtain ⟨hsz, hb⟩ := hg f rfl
  intro fo hfc f' hf'
  subst hf'
  obtain ⟨-, hl, -, -, -⟩ := hfc f' rfl
  have h8 : 8 ≤ f'.size := by simp only [initMeta] at hl; omega
  refine ⟨h8, fun b hb8 => ?_⟩
  have hx := durs_take8 f hsz hb8
  have hbl : b < ((f.contents.map durB).take 8).length := (List.getElem?_eq_some_iff.1 hx).1
  rw [List.getElem?_eq_getElem hbl, Option.some.injEq] at hx
  rw [crashed_dur hfc (List.mem_singleton_self _) (b := b) (x := f.cache b) (Nat.zero_le _)
    (by simpa using hbl) (by simp only [Nat.sub_zero, hx]) (by omega), ← (hb b hb8),
    contents_getElem?_of_lt (by omega)]

/-- The program's half: what `check` needs. -/
theorem start_check (f : OsFile) (hg : DataGood (some f)) :
    CheckOk (initMeta f) ((f.contents.map durB).take 8) := by
  obtain ⟨hsz, hb⟩ := hg f rfl
  refine ⟨hsz, by simp [contents_length]; omega, ?_⟩
  apply List.ext_getElem?
  intro b
  by_cases hb8 : b < 8
  · rw [List.getElem?_map, durs_take8 f hsz hb8, ← (hb b hb8), contents_getElem?_of_lt (by omega)]; rfl
  · have h1 : ((f.contents.map durB).take 8).length ≤ b := by simp; omega
    rw [List.getElem?_eq_none (by simpa using h1),
      List.getElem?_eq_none (by rw [dataC_length]; omega)]

theorem treeCrashed_nil {m : Tree} {V' : Hist} (h : TreeCrashed (m, []) V') : V' = (m, []) := by
  obtain ⟨n, hn, rfl⟩ := h
  simp only [List.length_nil, Nat.le_zero] at hn; subst hn; rfl

section gen
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

theorem osBytes_append' [L : GooseLocalGS GF] (i : Ino) (dq : DFrac) (off : Nat)
    (xs ys : List ByteG) :
    osBytes (L := L) i off dq (xs ++ ys) ⊣⊢
      osBytes (L := L) i off dq xs ∗ osBytes (L := L) i (off + xs.length) dq ys :=
  bytesG_append _ i dq off xs ys

/-- The file of the key `ko` as the generation `L` starts with it, `V` its history: `DataGood`,
and there if `seg` names it. -/
def startFile (L : GooseLocalGS GF) (j : Ino) (V : Hist) : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ fo, ⌜DataGood fo ∧ (V.now.entry j segB = some (.file k) → fo.isSome)⌝ ∗
      osFileStartO (L := L) k fo)

/-- The precondition of the boot program in the generation `L`, `dir` the root `R`'s directory
`j`. -/
def bootPre (R : Roots) (j : Ino) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (V : Hist) (ko : Option Ino), osTree (L := L) (DFrac.own 1) R V ∗
      ⌜SafeH j ko V ∧ MonoH j V⌝ ∗ startFile L j V ko)

/-- A generation's start, split between the invariant and the program, with a key that is the
file's or none. -/
theorem startFile_res [hG : HeapGS .hasLC GF] (j : Ino) (V : Hist) (ko : Option Ino)
    (hs : SafeH j ko V ∧ MonoH j V) :
    startFile hG.goose_localGS j V ko ⊢ ∃ ko', ⌜SafeH j ko' V ∧ MonoH j V⌝ ∗
      keyRes (L := hG.goose_localGS) ko' ∗ segRes (GF := GF) ko' := by
  cases ko with
  | none =>
    unfold startFile
    iintro -
    iexists none
    isplitr
    · ipureintro; exact hs
    unfold keyRes segRes; isplitl [] <;> iempintro
  | some k =>
    unfold startFile
    iintro ⟨%fo, %hfo, Hf⟩
    cases fo with
    | none =>
      -- the key's file is gone: `seg` names nothing now, and so in no crash
      have hn : V.now.entry j segB = none := by
        obtain ⟨-, -, h | ⟨k', hk', h⟩⟩ := safeH_now hs.1
        · exact h
        · cases hk'; exact absurd (hfo.2 h) (by simp)
      iexists none
      isplitr
      · ipureintro; exact ⟨safeH_rekey hs.1 (segNoneH_of hs.2 hn), hs.2⟩
      unfold keyRes segRes; isplitl [] <;> iempintro
    | some f =>
      unfold osFileStartO osFileStart
      icases Hf with ⟨Hm, Hb⟩
      icases (osMeta_halves (L := hG.goose_localGS) k _).1 $$ Hm with ⟨Hm1, Hm2⟩
      rw [← List.take_append_drop 8 (f.contents.map durB)]
      icases (osBytes_append' (L := hG.goose_localGS) k _ 0 _ _).1 $$ Hb with ⟨Hb, -⟩
      icases (osBytes_halves (L := hG.goose_localGS) k 0 _).1 $$ Hb with ⟨Hb1, Hb2⟩
      iexists (some k)
      isplitr
      · ipureintro; exact hs
      unfold keyRes segRes
      isplitl [Hm1 Hb1]
      · iexists _, _
        iframe Hm1 Hb1
        ipureintro; exact start_key f hfo.1
      · iexists _, _
        iframe Hm2 Hb2
        ipureintro; exact start_check f hfo.1

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
    exact lookupH_child hR hrj _ hb
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
    iexists (m0, []), ko0
    iframe Ht
    isplitr
    · ipureintro
      refine ⟨fun V' hc => ?_, fun V' hc => ?_⟩
      · rw [treeCrashed_nil hc]; exact hso.1
      · rw [treeCrashed_nil hc]; exact id
    cases ko0 with
    | none => unfold startFile; iempintro
    | some k =>
      have hk := hso.2 k rfl
      have hnm : Named (extLocal fsExt σ.world).fs.treeDur k := ⟨j, segB, by rw [hm0]; exact hk⟩
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (Hinit.2.2.2.2.2.1 k hnm)
      obtain ⟨vs, sz, hvs⟩ := (Hinit.2.2.2.2.2.2.1 k f hf).2
      have hgood : DataGood (some f) := by rw [← hf]; exact Hseg k hk
      icases (BigSepM.bigSepM_lookup
        (Φ := fun i f => osFileStart (L := hG.goose_localGS) i f) hf) $$ Hfs with Hf
      unfold startFile
      iexists (some f)
      isplitr
      · ipureintro; exact ⟨hgood, fun _ => rfl⟩
      unfold osFileStartO
      iexact Hf
  · -- every generation: the invariant, the boot program, and the next generation's
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPre
    iintro ⟨#Hos, Hgs, %V0, %ko, Ht, %hs, Hsf⟩ _
    icases startFile_res j V0 ko hs $$ Hsf with ⟨%ko0, %hs0, Hk, Hs⟩
    imod ghostVar_alloc (GF := GF) ko0 with ⟨%γ, Hv⟩
    icases (ghostVar_split_half (A := Option Ino) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases (_root_.Perennial.osTree_halves (L := hG.goose_localGS) R V0).1 $$ Ht with ⟨Ht1, Ht2⟩
    imod inv_alloc bootN ⊤ (iprop(∃ (V : Hist) (ko : Option Ino),
        osTree (L := hG.goose_localGS) (DFrac.own (1 : Qp).half) R V ∗
        ghostVar γ (1 : Qp).half ko ∗ ⌜SafeH j ko V ∧ MonoH j V⌝ ∗
        keyRes (L := hG.goose_localGS) ko)) $$ [Ht2 Hv1 Hk] with #Hinv
    · inext; iexists V0, ko0; iframe; ipureintro; exact hs0
    imodintro
    isplitl [Hgs Ht1 Hv2 Hs]
    · -- the boot program
      unfold boot
      wp_apply Hinit_wp $$ Hgs
      wp_pures
      wp_apply wp_Boot os.File.ReadAt.wp_proof os.File.Close.wp_proof os.File.WriteAt.wp_proof
          os.File.Fd.wp_proof syscall.Fdatasync.wp_proof R dir j γ V0 ko0 hR hrj (safeH_now hs0.1)
          $$ [Ht1 Hv2 Hs]
      · iframe; iframe #; unfold bootInv; iexact Hinv
      ipureintro; rfl
    · -- after a crash: the tree and the file from the old generation's invariant
      iintro %L' %V' _ #Hos' Hr Hgs'
      imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
        with ⟨Hi, Hclose⟩
      icases Hi with ⟨%W, %ko, >Ht, >Hv, >%Hp, >Hk⟩
      icases osTreeCrash_take (fun _ _ => True) hG.goose_localGS L' [] V' _ R W $$ Hr Ht
        with ⟨%hc, Ht', Hr, Ht⟩
      have hp' : SafeH j ko V' ∧ MonoH j V' := ⟨safeH_crash Hp.1 hc, monoH_crash Hp.2 hc⟩
      cases ko with
      | none =>
        imod Hclose $$ [Ht Hv Hk] with -
        · inext; iexists W, none; iframe; ipureintro; exact Hp
        imodintro
        iframe Hos' Hgs'
        iexists V', none
        iframe Ht'
        isplitr
        · ipureintro; exact hp'
        unfold startFile; iempintro
      | some k =>
        unfold keyRes
        icases Hk with ⟨%m, %bs, Hm, Hb, %hgood⟩
        icases osCrash_take_runs_keep (fun _ _ => True) hG.goose_localGS L' [] true V' k
          List.not_mem_nil _ m [(0, DFrac.own (1 : Qp).half, bs)] $$ Hr Hm [Hb]
          with ⟨%fo, %hfc, Hf, -, Hm, Hb⟩
        · iapply BigSepL.bigSepL_singleton.2; iexact Hb
        icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
        imod Hclose $$ [Ht Hv Hm Hb] with -
        · inext; iexists W, (some k); iframe Ht Hv
          isplitr
          · ipureintro; exact Hp
          dsimp only
          iexists m, bs
          iframe Hm
          isplitl [Hb]
          · iexact Hb
          ipureintro; exact hgood
        imodintro
        iframe Hos' Hgs'
        iexists V', (some k)
        iframe Ht'
        isplitr
        · ipureintro; exact hp'
        unfold startFile
        iexists fo
        iframe Hf
        ipureintro
        exact ⟨hgood fo hfc.1, fun h => hfc.2.1 ⟨j, segB, h⟩⟩

/-- **Crash safety of `examples/osfs/walfs`'s `segdir.Boot`.** In every execution with crashes of
the boot program (`RealCrashNsteps`, the real semantics; a crash of the machine, a restart of the
process alone being one under the semantics' "Restarts" assumption), from a state whose Go context satisfies the Go semantics and the package's assumptions,
with no package initialized, the main thread only, the Linux file extension's state as on disk
(`FsInit`), `dir` one of its roots, in which neither `dir/seg` nor `dir/seg.tmp` is a directory and
`dir/seg`, if it names a file, names one that is `DataGood` (the 8 bytes of data at 0, clean): the
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
