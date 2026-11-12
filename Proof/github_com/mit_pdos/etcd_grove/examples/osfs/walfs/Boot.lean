/-
The proofs of `examples/osfs/walfs`'s `segdir.go` (one generation), over the file extension v2: the
crash invariant of the directory `dir` (a root, of inode `j`) and of the file its entry `seg`
names, and the specs of `Boot` and its helpers.

The invariant (`bootInv`) holds half of the directory tree's history and says what every crash of
it (`TreeCrashed`: a restart keeps the history, a machine crash a prefix of it) may name `seg` and
`seg.tmp` in `dir` (`SafeT`): neither a directory, and `seg` nothing or the file of the key `ko`, a
ghost variable whose other half the program keeps, with half of that file's `OsMeta` and bytes,
every crash of which leaves the data (`DataGood`: the 8 bytes at 0; the invariant holds them
durable, so that every crash keeps them). `seg` never goes once it is
there (`MonoH`), so that, absent now, it is absent from every crash. The program opens the
invariant around each call that changes the directory (`unlink`, `rmdir`, `open(O_CREAT)`,
`rename`), and before the rename deposits the new file, written and made durable, under the key
`seg.tmp` names.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs
public import Proof.os.Ns
public import Proof.os.CrashWrite
public import Spec.os.File__ReadAt
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.os.File__Close
public import Spec.syscall.Fdatasync
public import GooseLang.Ext.Fs.TreeSpecsMeta
public import Perennial.Std.Namespaces

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs
open Fs

/-! ## The names and the data -/

def segB : GoString := go!"seg"
def tmpB : GoString := go!"seg.tmp"

theorem segB_ok : NameOk segB := by decide
theorem tmpB_ok : NameOk tmpB := by decide
theorem tmp_ne_seg : tmpB ≠ segB := by decide

/-- The data of a committed segment (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

/-- What a crash may leave of the file `seg` names: no file, or the data at 0. -/
def DataGood (fo : Option OsFile) : Prop :=
  ∀ f, fo = some f → 8 ≤ f.size ∧ ∀ b < 8, f.contents[b]? = dataC[b]?

theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {b : α}
    (hb : l[i]? = some b) : b ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
  have hji : j < i := by simp at hj; omega
  have hil : i < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have hjl : j < l.length := by omega
  have e1 : l[j] = b := by rw [← hjb, List.getElem_take]
  have e2 : l[i] = b := (List.getElem?_eq_some_iff.1 hb).2
  exact List.pairwise_iff_getElem.1 h j i hjl hil hji (e1.trans e2.symm)

/-! ## What every crash of the tree must be -/

/-- **The tree a boot may find**, in the directory `j`: neither `seg` nor `seg.tmp` a directory;
`seg` nothing, or the file of the key `ko`. -/
def SafeT (j : Ino) (ko : Option Ino) (m : Tree) : Prop :=
  (∀ J, m.entry j segB ≠ some (.dir J)) ∧ (∀ J, m.entry j tmpB ≠ some (.dir J)) ∧
  (m.entry j segB = none ∨ ∃ k, ko = some k ∧ m.entry j segB = some (.file k))

/-- Every crash of the history `V` is `SafeT`. -/
def SafeH (j : Ino) (ko : Option Ino) (V : Hist) : Prop := ∀ V', TreeCrashed V V' → SafeT j ko V'.now

/-- `seg`, in a crash of `V`, is in `V` now: it never goes. -/
def MonoH (j : Ino) (V : Hist) : Prop :=
  ∀ V', TreeCrashed V V' → V'.now.entry j segB ≠ none → V.now.entry j segB ≠ none

/-- No crash of `V` has anything at `seg`. -/
def SegNoneH (j : Ino) (V : Hist) : Prop := ∀ V', TreeCrashed V V' → V'.now.entry j segB = none

theorem safeH_now {j : Ino} {ko : Option Ino} {V : Hist} (h : SafeH j ko V) : SafeT j ko V.now :=
  h (V.now, []) (treeCrashed_refl V)

theorem safeH_push {j : Ino} {ko : Option Ino} {V : Hist} {e : LogEntry} (h : SafeH j ko V)
    (he : SafeT j ko (e.op.apply V.now)) : SafeH j ko (V.push e) := by
  intro V' hc
  rcases treeCrashed_push hc with hc | hn
  · exact h V' hc
  · rw [hn, Hist.push_now]; exact he

theorem monoH_push {j : Ino} {V : Hist} {e : LogEntry} (h : MonoH j V)
    (he : V.now.entry j segB ≠ none → (e.op.apply V.now).entry j segB ≠ none) :
    MonoH j (V.push e) := by
  intro V' hc hs
  rw [Hist.push_now]
  rcases treeCrashed_push hc with hc | hn
  · exact he (h V' hc hs)
  · rw [hn, Hist.push_now] at hs; exact hs

theorem segNoneH_of {j : Ino} {V : Hist} (h : MonoH j V) (hn : V.now.entry j segB = none) :
    SegNoneH j V := by
  intro V' hc
  by_cases hs : V'.now.entry j segB = none
  · exact hs
  · exact absurd hn (h V' hc hs)

/-- With nothing at `seg` in any crash, the key does not matter. -/
theorem safeH_rekey {j : Ino} {ko ko' : Option Ino} {V : Hist} (h : SafeH j ko V)
    (hn : SegNoneH j V) : SafeH j ko' V := by
  intro V' hc
  obtain ⟨h1, h2, -⟩ := h V' hc
  exact ⟨h1, h2, .inl (hn V' hc)⟩

/-- A crash of a crash is a crash. -/
theorem treeCrashed_trans {V V' V'' : Hist} (h1 : TreeCrashed V V') (h2 : TreeCrashed V' V'') :
    TreeCrashed V V'' := Fs.treeCrashed_trans h1 h2

theorem safeH_crash {j : Ino} {ko : Option Ino} {V V' : Hist} (h : SafeH j ko V)
    (hc : TreeCrashed V V') : SafeH j ko V' := fun V'' hc' => h V'' (treeCrashed_trans hc hc')

theorem monoH_crash {j : Ino} {V V' : Hist} (h : MonoH j V) (hc : TreeCrashed V V') : MonoH j V' := by
  intro V'' hc' hs
  obtain ⟨n, hn, rfl⟩ := hc
  obtain ⟨n', hn', rfl⟩ := hc'
  have : n' = 0 := by simpa using hn'
  subst this
  simpa [replay, Hist.now, Hist.ops] using hs

/-! ## The operations on `seg.tmp` and `seg` -/

theorem entry_upd (m : Tree) (j : Ino) (f : Dir → Dir) (j' : Ino) (y : GoString) :
    (m.upd j f).entry j' y = if j = j' then f (entsOf m j) !! y else m.entry j' y := by
  rw [← entsOf_lookup]
  by_cases hj : j = j'
  · subst hj; rw [entsOf_upd_eq, if_pos rfl]
  · rw [entsOf_upd_ne _ _ hj, entsOf_lookup, if_neg hj]

theorem entry_create (m : Tree) (j : Ino) (x : GoString) (i : Ino) (j' : Ino) (y : GoString) :
    ((MetaOp.create j x i).apply m).entry j' y =
      if j = j' ∧ x = y then some (.file i) else m.entry j' y := by
  simp only [MetaOp.apply]
  rw [entry_upd]
  by_cases hj : j = j'
  · subst hj; by_cases hx : x = y
    · subst hx; simp
    · simp [hx, ← entsOf_lookup]
  · simp [hj]

theorem entry_remove (m : Tree) (j : Ino) (x : GoString) (n : Node) (j' : Ino) (y : GoString) :
    ((MetaOp.remove j x n).apply m).entry j' y = if j = j' ∧ x = y then none else m.entry j' y := by
  simp only [MetaOp.apply]
  rw [entry_upd]
  by_cases hj : j = j'
  · subst hj; by_cases hx : x = y
    · subst hx; simp
    · simp [hx, ← entsOf_lookup]
  · simp [hj]

/-- A rename within the directory `j` of the entry `x`, naming `n`, to `y`. -/
theorem entry_rename (m : Tree) (j : Ino) (x y : GoString) (n : Node) (old : Option Node)
    (hn : m.entry j x = some n) (hxy : x ≠ y) (j' : Ino) (z : GoString) :
    ((MetaOp.rename j x j y n old).apply m).entry j' z =
      if j = j' ∧ y = z then some n else if j = j' ∧ x = z then none else m.entry j' z := by
  simp only [MetaOp.apply, hn]
  rw [entry_upd]
  by_cases hj : j = j'
  · subst hj
    rw [if_pos rfl, entsOf_upd_eq]
    by_cases hz : y = z
    · subst hz; simp
    · by_cases hx : x = z
      · subst hx; simp [hz]
      · simp [hz, hx, ← entsOf_lookup]
  · rw [if_neg hj, entry_upd, if_neg hj]; simp [hj]

/-- A change of `seg.tmp` keeps `SafeT` (a file there, or nothing) and leaves `seg`. -/
theorem safeT_create_tmp {j : Ino} {ko : Option Ino} {m : Tree} (h : SafeT j ko m) (i : Ino) :
    SafeT j ko ((MetaOp.create j tmpB i).apply m) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : ((MetaOp.create j tmpB i).apply m).entry j segB = m.entry j segB := by
    rw [entry_create]; simp [tmp_ne_seg]
  have ht : ((MetaOp.create j tmpB i).apply m).entry j tmpB = some (.file i) := by
    rw [entry_create]; simp
  refine ⟨fun J => by rw [hs]; exact h1 J, fun J => by rw [ht]; simp, by rw [hs]; exact h3⟩

theorem safeT_remove_tmp {j : Ino} {ko : Option Ino} {m : Tree} (h : SafeT j ko m) (n : Node) :
    SafeT j ko ((MetaOp.remove j tmpB n).apply m) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : ((MetaOp.remove j tmpB n).apply m).entry j segB = m.entry j segB := by
    rw [entry_remove]; simp [tmp_ne_seg]
  have ht : ((MetaOp.remove j tmpB n).apply m).entry j tmpB = none := by
    rw [entry_remove]; simp
  refine ⟨fun J => by rw [hs]; exact h1 J, fun J => by rw [ht]; simp, by rw [hs]; exact h3⟩

theorem seg_create_tmp (m : Tree) (j i : Ino) :
    ((MetaOp.create j tmpB i).apply m).entry j segB = m.entry j segB := by
  rw [entry_create]; simp [tmp_ne_seg]

theorem seg_remove_tmp (m : Tree) (j : Ino) (n : Node) :
    ((MetaOp.remove j tmpB n).apply m).entry j segB = m.entry j segB := by
  rw [entry_remove]; simp [tmp_ne_seg]

/-- **The rename of `seg.tmp`, the file of `k`, onto `seg`** (nothing or a file): `SafeT` with the
key `k`. -/
theorem safeT_rename {j k : Ino} {ko : Option Ino} {m : Tree} (h : SafeT j ko m)
    (hk : m.entry j tmpB = some (.file k)) (old : Option Node) :
    SafeT j (some k) ((MetaOp.rename j tmpB j segB (.file k) old).apply m) := by
  have hs := entry_rename m j tmpB segB (.file k) old hk tmp_ne_seg j segB
  have ht := entry_rename m j tmpB segB (.file k) old hk tmp_ne_seg j tmpB
  simp only [and_self, ite_true] at hs
  rw [if_neg (by simp [Ne.symm tmp_ne_seg]), if_pos (by simp)] at ht
  exact ⟨fun J => by rw [hs]; simp, fun J => by rw [ht]; simp, .inr ⟨k, rfl, hs⟩⟩

theorem seg_rename (m : Tree) (j k : Ino) (old : Option Node) (hk : m.entry j tmpB = some (.file k)) :
    ((MetaOp.rename j tmpB j segB (.file k) old).apply m).entry j segB = some (.file k) := by
  have hs := entry_rename m j tmpB segB (.file k) old hk tmp_ne_seg j segB
  simpa using hs

/-! ## Paths -/

/-- The root `d` names its directory, whatever the history. -/
theorem lookupH_root {R : Roots} (hr : RootsOk R) {d : GoString} {j : Ino} (hd : (d, j) ∈ R)
    (V : Hist) : lookupH R V d = some (.dir j) := by
  have := lookup_joinPath (st := Hist.st R V) hr hd (cs := []) (by simp)
  simp only [joinPath, List.flatMap_nil, List.append_nil, walk] at this
  exact this

/-- A name in the root `d`: the entry of its directory. -/
theorem lookupH_child {R : Roots} (hr : RootsOk R) {d : GoString} {j : Ino} (hd : (d, j) ∈ R)
    (V : Hist) {b : GoString} (hb : NameOk b) : lookupH R V (child d b) = V.now.entry j b :=
  lookup_child (st := Hist.st R V) hr (lookupH_root hr hd V) hb

/-! ## The invariant -/

theorem qp3 : ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half = 1 :=
  Subtype.ext (by grind)

/-- The operations of the program on `seg.tmp` keep `SafeH` and `MonoH`. -/
theorem inv_remove_tmp {j : Ino} {ko : Option Ino} {V : Hist} (h : SafeH j ko V ∧ MonoH j V)
    (n : Node) (s : Nat) :
    SafeH j ko (V.push ⟨.remove j tmpB n, s⟩) ∧ MonoH j (V.push ⟨.remove j tmpB n, s⟩) :=
  ⟨safeH_push h.1 (safeT_remove_tmp (safeH_now h.1) n),
   monoH_push h.2 (by
     intro h'; show ((MetaOp.remove j tmpB n).apply V.now).entry j segB ≠ none
     rw [seg_remove_tmp]; exact h')⟩

theorem inv_create_tmp {j : Ino} {ko : Option Ino} {V : Hist} (h : SafeH j ko V ∧ MonoH j V)
    (i : Ino) (s : Nat) :
    SafeH j ko (V.push ⟨.create j tmpB i, s⟩) ∧ MonoH j (V.push ⟨.create j tmpB i, s⟩) :=
  ⟨safeH_push h.1 (safeT_create_tmp (safeH_now h.1) i),
   monoH_push h.2 (by
     intro h'; show ((MetaOp.create j tmpB i).apply V.now).entry j segB ≠ none
     rw [seg_create_tmp]; exact h')⟩

theorem inv_rename {j k : Ino} {V : Hist} (h : SafeH j (some k) V ∧ MonoH j V)
    (hk : V.now.entry j tmpB = some (.file k)) (old : Option Node) (s : Nat) :
    SafeH j (some k) (V.push ⟨.rename j tmpB j segB (.file k) old, s⟩) ∧
      MonoH j (V.push ⟨.rename j tmpB j segB (.file k) old, s⟩) :=
  ⟨safeH_push h.1 (safeT_rename (safeH_now h.1) hk old),
   monoH_push h.2 (fun _ => by
     show ((MetaOp.rename j tmpB j segB (.file k) old).apply V.now).entry j segB ≠ none
     rw [seg_rename _ _ _ _ hk]; simp)⟩

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant's half of the file of the key `ko`: of its `OsMeta` and bytes, every crash of
which is `DataGood`. -/
def keyRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List ByteG),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗
      ⌜∀ fo, FileCrashedR m [(0, DFrac.own (1 : Qp).half, bs)] fo → DataGood fo⌝)

instance keyRes_timeless (ko : Option Ino) : Timeless (keyRes (L := L) ko) := by
  cases ko <;> unfold keyRes <;> unfold osMeta osBytes bytesG <;> infer_instance

def bootN : Namespace := nroot .@ "walfs"

theorem bootN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑bootN := mask_ndot_ne' nroot "osfs" "walfs" (by decide)

/-- **The crash invariant** of the directory `j` (in the roots `R`). -/
def bootInv (R : Roots) (j : Ino) (γ : GName) : IProp GF :=
  inv bootN iprop(∃ (V : Hist) (ko : Option Ino),
    osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ghostVar γ (1 : Qp).half ko ∗
    ⌜SafeH j ko V ∧ MonoH j V⌝ ∗ keyRes (L := L) ko)

instance bootInv_persistent (R : Roots) (j : Ino) (γ : GName) :
    Persistent (bootInv (L := L) R j γ) := by
  unfold bootInv; infer_instance

/-- The invariant opened around a step that keeps the key: the invariant's half of the history
with the caller's quarter, and what closes it again with a history still `SafeH` and `MonoH`. -/
theorem boot_acc (R : Roots) (j : Ino) (γ : GName) (V : Hist) :
    ⊢ bootInv (L := L) R j γ -∗ osTree (L := L) (DFrac.own (1 : Qp).half.half) R V
      ={⊤, ⊤ \ ↑bootN}=∗ ∃ ko, osTree (L := L) (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) R V ∗
        ⌜SafeH j ko V ∧ MonoH j V⌝ ∗
        (∀ V', ⌜SafeH j ko V' ∧ MonoH j V'⌝ -∗ osTree (L := L) (DFrac.own 1) R V' ={⊤ \ ↑bootN, ⊤}=∗
          osTree (L := L) (DFrac.own (1 : Qp).half) R V') := by
  iintro #Hinv Ht
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko, >Ht1, >Hv, >%Hs, >Hk⟩
  icases osTree_agree (L := L) _ _ R R V V1 $$ Ht Ht1 with %he
  obtain ⟨-, rfl⟩ := he
  ihave Hw := (osTree_split (L := L) (1 : Qp).half (1 : Qp).half.half R V).2 $$ [Ht1 Ht]
  · iframe
  imodintro
  iexists ko
  iframe Hw
  isplitr
  · ipureintro; exact Hs
  iintro %V' %Hs' Ht'
  icases (_root_.Perennial.osTree_halves R V').1 $$ Ht' with ⟨Ht1, Ht2⟩
  imod Hclose $$ [Ht1 Hv Hk] with -
  · inext; iexists V', ko; iframe; ipureintro; exact Hs'
  imodintro
  iexact Ht2

end res

/-! ## A rename within one directory, between two names -/

section ren
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`rename(2)` of the file `d/bs` to `d/bt`**, two names of one directory (`wp_osRenameFileG`
without its rename of an entry to itself, which two names exclude): the operation logged, on a
failure logged or not. -/
theorem wp_osRenameFileSame (d bs bt : GoString) (j i : Ino) (hbs : NameOk bs) (hbt : NameOk bt)
    (hne : bs ≠ bt) (R : Roots) (V : Hist) (q1 q : Qp) (k s' : Nat) (hq : q1 + q = 1)
    (hd : lookupH R V d = some (.dir j)) (hs : lookupH R V (child d bs) = some (.file i))
    (ht : ∀ J, lookupH R V (child d bt) ≠ some (.dir J)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜RenameDirPost V (renameOp R V j bs j d bt (.file i)) e V'⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Rename" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    exact ⟨_, st.metaEnd k, ⟨child d bs, child d bt, k, s', rfl, treeName_child hdd hbs,
      treeName_child hdd hbt, by rw [hp.calls]; simp,
      fun _ k'' s'' h => by rw [hp.calls] at h; simp at h; exact h.1.symm,
      .inr (.inr ⟨W64 1, by decide, rfl, rfl⟩)⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hss : st.lookup (child d bs) = some (.file i) := (lookup_pre hp _).trans hs
    have hroots := hp.wf.roots
    obtain ⟨htw, -, hlt⟩ := wf_tree hp.wf
    obtain ⟨s0, t0, k', start, hv, -, -, hk', -, hres⟩ := hst
    obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨-, o, ho, hr⟩ | ⟨hst', -, -, -⟩ | ⟨e, he, rfl, rfl⟩
    · obtain rfl := renameOp_eq hp hbs hbt hdd hdd hss ho
      have hent : st.tree.entry j bs = some (.file i) := by
        rw [← lookup_child hroots hdd hbs]; exact hss
      have hnt : ∀ J, st.tree.entry j bt ≠ some (.dir J) := fun J => by
        rw [← lookup_child hroots hdd hbt, lookup_pre hp]; exact ht J
      have hpost := metaPost_doEnd hp (renameOp R V j bs j d bt (.file i))
        (treeWf_renameFile htw (reach_of_lookup hdd) (reach_of_lookup hdd) hbt hent hnt _ _)
        (named_rename _ _ _ _ _ _ _)
        (fun x hx => by
          rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hdd))
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hdd))
          · exact hlt _ hx)
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨0, rfl, hpost.1, .inl ⟨rfl, hpost.2⟩⟩
      · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, .inl (metaPost_end hp).2⟩⟩
      · exact ⟨e, rfl, hpost.1, .inr ⟨he, .inr hpost.2⟩⟩
    · exact absurd (child_inj hst') hne
    · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, .inl (metaPost_end hp).2⟩⟩

end ren

/-! ## The calls that change the directory, with the invariant -/

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- `unlink(2)` of `seg.tmp`, the invariant opened around it. -/
theorem wp_unlinkTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (k s : Nat)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗ osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ (e : w64) (V' : Hist), ⌜UnlinkPost R V d tmpB j e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d tmpB))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc R j γ V $$ Hinv Ht with ⟨%ko, Ht, %Hs, Hclose⟩
  imodintro
  iapply wp_osUnlinkG d tmpB j tmpB_ok R V _ _ k s qp3 (lookupH_root hr hd V) bootN_disj
    $$ Hos Ht Hk
  iintro %e %V' %hp Ht
  have hs' : SafeH j ko V' ∧ MonoH j V' := by
    rcases hp with ⟨i, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩
    · exact inv_remove_tmp Hs _ _
    · exact Hs
    · exact inv_remove_tmp Hs _ _
    · exact Hs
  imod Hclose $$ %V' %hs' Ht with Ht
  imodintro
  iapply HΦ $$ %e %V' %hp Ht

/-- `rmdir(2)` of `seg.tmp`, the invariant opened around it. -/
theorem wp_rmdirTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (k s : Nat)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗ osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ (e : w64) (V' : Hist), ⌜RmdirPost R V d tmpB j e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d tmpB))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc R j γ V $$ Hinv Ht with ⟨%ko, Ht, %Hs, Hclose⟩
  imodintro
  iapply wp_osRmdirG d tmpB j tmpB_ok R V _ _ k s qp3 (lookupH_root hr hd V) bootN_disj
    $$ Hos Ht Hk
  iintro %e %V' %hp Ht
  have hs' : SafeH j ko V' ∧ MonoH j V' := by
    rcases hp with ⟨J, -, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩
    · exact inv_remove_tmp Hs _ _
    · exact Hs
    · exact inv_remove_tmp Hs _ _
    · exact Hs
  imod Hclose $$ %V' %hs' Ht with Ht
  imodintro
  iapply HΦ $$ %e %V' %hp Ht

/-- `open(2)` with `O_RDWR | O_CREAT` of `seg.tmp`, absent, the invariant opened around it. -/
theorem wp_createTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (k s : Nat)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hn : V.now.entry j tmpB = none) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗ osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ fd : w64, ∀ e : w64,
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ i,
            osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create j tmpB i, V.2.length⟩) ∗
            osMeta (GF := GF) i (DFrac.own 1) newMeta ∗ osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∨ ∃ i,
            osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create j tmpB i, V.2.length⟩) ∗
            osMeta (GF := GF) i (DFrac.own 1) newMeta))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d tmpB)) (#flCreat)))))
        {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk HΦ
  have hn' : lookupH R V (child d tmpB) = none := by rw [lookupH_child hr hd V tmpB_ok]; exact hn
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc R j γ V $$ Hinv Ht with ⟨%ko, Ht, %Hs, Hclose⟩
  imodintro
  iapply wp_osOpenCreate d tmpB R V _ _ k s j tmpB_ok (lookupH_root hr hd V) hn' qp3
    bootN_disj $$ Hos Ht Hk
  iintro %fd %e %- Hres
  icases Hres with (⟨%he, %i, Ht, Hm, Hfd⟩ | ⟨%he, (Ht | ⟨%i, Ht, Hm⟩)⟩)
  · imod Hclose $$ %_ %(inv_create_tmp Hs i _) Ht with Ht
    imodintro
    iapply HΦ; ileft; iframe; ipureintro; exact he
  · imod Hclose $$ %V %Hs Ht with Ht
    imodintro
    iapply HΦ; iright; iframe; ipureintro; exact he
  · imod Hclose $$ %_ %(inv_create_tmp Hs i _) Ht with Ht
    imodintro
    iapply HΦ; iright; isplitr
    · ipureintro; exact he
    iright; iexists i; iframe

/-- `rename(2)` of `seg.tmp`, the file of `k`, onto `seg`, the invariant's key `k`, the invariant
opened around it. -/
theorem wp_renameTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (k s i : Nat)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hk : V.now.entry j tmpB = some (.file i))
    (hns : ∀ J, V.now.entry j segB ≠ some (.dir J)) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗ osCall (GF := GF) k s (1 : Qp).half.half -∗
      ghostVar (GF := GF) γ (1 : Qp).half (some i) -∗
      (∀ (e : w64) (V' : Hist),
        ⌜RenameDirPost V (renameOp R V j tmpB j d segB (.file i)) e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ ghostVar (GF := GF) γ (1 : Qp).half (some i) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d tmpB)) (#(child d segB)))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  have hs : lookupH R V (child d tmpB) = some (.file i) := by
    rw [lookupH_child hr hd V tmpB_ok]; exact hk
  have ht : ∀ J, lookupH R V (child d segB) ≠ some (.dir J) := by
    intro J; rw [lookupH_child hr hd V segB_ok]; exact hns J
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko, >Ht1, >Hv, >%Hs, >Hkr⟩
  icases osTree_agree (L := hG.goose_localGS) _ _ R R V V1 $$ Ht Ht1 with %he
  obtain ⟨-, rfl⟩ := he
  icases ghostVar_agree _ _ _ _ _ $$ Hγ Hv with %hko
  subst hko
  ihave Hw := (osTree_split (L := hG.goose_localGS) (1 : Qp).half (1 : Qp).half.half R V).2 $$ [Ht1 Ht]
  · iframe
  imodintro
  iapply wp_osRenameFileSame d tmpB segB j i tmpB_ok segB_ok tmp_ne_seg R V _ _ k s qp3
    (lookupH_root hr hd V) hs ht bootN_disj $$ Hos Hw Hk
  iintro %e %V' %hp Ht'
  have hs' : SafeH j (some i) V' ∧ MonoH j V' := by
    rcases hp with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
    · exact inv_rename Hs hk _ _
    · exact Hs
    · exact inv_rename Hs hk _ _
  icases (_root_.Perennial.osTree_halves R V').1 $$ Ht' with ⟨Ht1, Ht2⟩
  imod Hclose $$ [Ht1 Hv Hkr] with -
  · inext; iexists V', (some i); iframe; ipureintro; exact hs'
  imodintro
  iapply HΦ $$ %e %V' %hp Ht2 Hγ

end steps

/-! ## `os` calls on `seg.tmp` and `seg`, with the invariant -/

theorem seg_unlinkPost {R : Roots} {V V' : Hist} {d : GoString} {j : Ino} {e : w64}
    (h : UnlinkPost R V d tmpB j e V') : V'.now.entry j segB = V.now.entry j segB := by
  rcases h with ⟨i, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩ <;>
    first | rfl | (rw [Hist.push_now]; exact seg_remove_tmp _ _ _)

theorem seg_rmdirPost {R : Roots} {V V' : Hist} {d : GoString} {j : Ino} {e : w64}
    (h : RmdirPost R V d tmpB j e V') : V'.now.entry j segB = V.now.entry j segB := by
  rcases h with ⟨J, -, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩ <;>
    first | rfl | (rw [Hist.push_now]; exact seg_remove_tmp _ _ _)

theorem tmp_removed {V : Hist} {j : Ino} {n : Node} {s : Nat} :
    (V.push ⟨.remove j tmpB n, s⟩).now.entry j tmpB = none := by
  rw [Hist.push_now]; show ((MetaOp.remove j tmpB n).apply V.now).entry j tmpB = none
  rw [entry_remove]; simp

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.Remove(d/seg.tmp)`: `seg` as it was; on success nothing at `seg.tmp`. -/
theorem wp_removeTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist)
    (hr : RootsOk R) (hd : (d, j) ∈ R) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) R j γ ∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V }}
      (App (Val (@! os.Remove)) (Val #(child d tmpB)))
    {{ (err : GoInterface), RET #err; ∃ V', osTree (DFrac.own (1 : Qp).half) R V' ∗
        ⌜V'.now.entry j segB = V.now.entry j segB ∧ (err = interface.nil → V'.now.entry j tmpB = none)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Ht⟩
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = V := ⟨_, rfl⟩
  ihave Ht : osTree (DFrac.own (1 : Qp).half) R V1 $$ [Ht]
  · subst hV1; iexact Ht
  ihave Hp : ⌜V1.now.entry j segB = V.now.entry j segB⌝ $$ []
  · ipureintro; rw [hV1]
  clear hV1
  iloeb as IH generalizing %V1 Hp Ht
  icases Hp with %Hp
  icases (osTree_halves (1 : Qp).half R V1).1 $$ Ht with Ht
  wp_apply wp_osCallBegin R V1 _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
  (try wp_auto)
  wp_apply wp_unlinkTmp R d j γ V1 t _ hr hd $$ Hos Hinv Ht Hk as %e %V' %hres Ht
  have hs' : V'.now.entry j segB = V.now.entry j segB := (seg_unlinkPost hres).trans Hp
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V' [] Ht HΦ
    ipureintro; exact hs'
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iexists V'
    iframe Ht
    ipureintro
    refine ⟨hs', fun _ => ?_⟩
    rcases hres with ⟨i, -, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩
    · exact tmp_removed
    · exact absurd he0 h
    · exact absurd he0 h
  rw [decide_eq_false he0]
  wp_auto
  clear hres
  ihave Hp2 : ⌜V'.now.entry j segB = V.now.entry j segB⌝ $$ []
  · ipureintro; exact hs'
  clear hs'
  iloeb as IH2 generalizing %V' Hp2 Ht
  icases Hp2 with %hs'
  icases (osTree_halves (1 : Qp).half R V').1 $$ Ht with Ht
  wp_apply wp_osCallBegin R V' _ _ CoPset.subseteq_top $$ Hos Ht as %t1 Ht Hk
  (try wp_auto)
  wp_apply wp_rmdirTmp R d j γ V' t1 _ hr hd $$ Hos Hinv Ht Hk as %e1 %V2 %hres1 Ht
  have hs2 : V2.now.entry j segB = V.now.entry j segB := (seg_rmdirPost hres1).trans hs'
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ %V2 [] Ht HΦ
    ipureintro; exact hs2
  rw [decide_eq_false he14]
  wp_auto
  by_cases he10 : e1 = W64 0
  · rw [decide_eq_true he10]
    wp_auto
    iapply HΦ
    iexists V2
    iframe Ht
    ipureintro
    refine ⟨hs2, fun _ => ?_⟩
    rcases hres1 with ⟨J, -, -, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩
    · exact tmp_removed
    · exact absurd he10 h
    · exact absurd he10 h
  rw [decide_eq_false he10]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iexists V2
    iframe Ht
    ipureintro; exact ⟨hs2, fun h => by cases h⟩
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iexists V2
    iframe Ht
    ipureintro; exact ⟨hs2, fun h => by cases h⟩

end oscalls


theorem tmp_created {V : Hist} {j i : Ino} {s : Nat} :
    (V.push ⟨.create j tmpB i, s⟩).now.entry j tmpB = some (.file i) := by
  rw [Hist.push_now]; show ((MetaOp.create j tmpB i).apply V.now).entry j tmpB = _
  rw [entry_create]; simp

theorem seg_created {V : Hist} {j i : Ino} {s : Nat} :
    (V.push ⟨.create j tmpB i, s⟩).now.entry j segB = V.now.entry j segB := by
  rw [Hist.push_now]; exact seg_create_tmp _ _ _

section oscalls2
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- What a retried create of `seg.tmp` sees: nothing there, or the file it made. -/
def crState (R : Roots) (V : Hist) (j : Ino) : Option Ino → IProp GF
  | none => osTree (GF := GF) (DFrac.own (1 : Qp).half) R V
  | some i => iprop(osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create j tmpB i, V.2.length⟩) ∗
      osMeta (GF := GF) i (DFrac.own 1) newMeta)

/-- `os.OpenFile(d/seg.tmp, O_RDWR|O_CREATE, perm)`, `seg.tmp` absent: on success a new file
`seg.tmp` names; `seg` as it was in any case. -/
theorem wp_openTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hn : V.now.entry j tmpB = none) (perm : w32) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) R j γ ∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d tmpB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil⌝ ∗
            os.ownFile f fd (child d tmpB) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗
            osMeta i (DFrac.own 1) newMeta ∗
            osTree (DFrac.own (1 : Qp).half) R (V.push ⟨.create j tmpB i, V.2.length⟩)) ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ V', osTree (DFrac.own (1 : Qp).half) R V' ∗
            ⌜V'.now.entry j segB = V.now.entry j segB⌝)) }} := by
  wp_start as ⟨#Hos, #Hinv, Hh⟩
  obtain ⟨o, ho⟩ : ∃ o : Option Ino, o = none := ⟨none, rfl⟩
  ihave Hh := (show osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ⊢ crState R V j o by
    rw [ho]; exact .rfl) $$ Hh
  clear ho
  iloeb as IH generalizing %o Hh HΦ
  cases o with
  | none =>
    unfold crState
    ihave Hh := (osTree_halves (1 : Qp).half R V).1 $$ Hh
    wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Hh as %t Hh Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_createTmp R d j γ V t _ hr hd hn $$ Hos Hinv Hh Hk as %fd %e Hres
    icases Hres with (⟨%he, %i, Hh, Hm, Hfd⟩ | ⟨%he, Hst⟩)
    · obtain ⟨rfl, hfd0⟩ := he
      rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; rfl
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        icases Hst with (Hh | ⟨%i, Hh, Hm⟩)
        · iapply IH $$ %none Hh HΦ
        · iapply IH $$ %(some i) [Hh Hm] HΦ
          (try dsimp only); iframe
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        icases Hst with (Hh | ⟨%i, Hh, -⟩)
        · iexists V; iframe; ipureintro; rfl
        · iexists _; iframe; ipureintro; exact seg_created
  | some i =>
    unfold crState
    icases Hh with ⟨Hh, Hm⟩
    have hl : lookupH R (V.push ⟨.create j tmpB i, V.2.length⟩) (child d tmpB) = some (.file i) := by
      rw [lookupH_child hr hd _ tmpB_ok]; exact tmp_created
    ihave Hh := (osTree_halves (1 : Qp).half R _).1 $$ Hh
    wp_apply wp_osCallBegin R _ _ _ CoPset.subseteq_top $$ Hos Hh as %t Hh Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
    (try wp_auto)
    wp_apply wp_osOpenFile (child d tmpB) (W64 0x80042) R _ _ _ t _ i
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hl
      CoPset.subseteq_top $$ Hos Hh Hk as %fd %e %hres Hh Hfd
    ihave Hh := (osTree_halves (1 : Qp).half R _).2 $$ Hh
    by_cases he0 : e = W64 0
    · subst he0
      rw [decide_eq_true rfl]
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i (W64 0x80042)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨i, true, true⟩
        by rw [openFd_rw]; split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; rfl
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · rw [decide_eq_false he0]
      iclear Hfd
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %(some i) [Hh Hm] HΦ
        (try dsimp only); iframe
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists _; iframe; ipureintro; exact seg_created

end oscalls2


theorem tmp_renamed {V : Hist} {j i : Ino} {old : Option Node} {s : Nat}
    (hk : V.now.entry j tmpB = some (.file i)) :
    (V.push ⟨.rename j tmpB j segB (.file i) old, s⟩).now.entry j tmpB = none := by
  rw [Hist.push_now]
  have ht := entry_rename V.now j tmpB segB (.file i) old hk tmp_ne_seg j tmpB
  rw [if_neg (by simp [Ne.symm tmp_ne_seg]), if_pos (by simp)] at ht
  exact ht

theorem seg_renamed {V : Hist} {j i : Ino} {old : Option Node} {s : Nat}
    (hk : V.now.entry j tmpB = some (.file i)) :
    (V.push ⟨.rename j tmpB j segB (.file i) old, s⟩).now.entry j segB = some (.file i) := by
  rw [Hist.push_now]; exact seg_rename _ _ _ _ hk

section oscalls3
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]

/-- `rename(2)` of `seg.tmp`, absent, the invariant opened around it: it fails, the tree as it
was. -/
theorem wp_renameAbsentTmp (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (k s : Nat)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hn : V.now.entry j tmpB = none) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗ osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ (e : w64), ⌜e ≠ 0⌝ -∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d tmpB)) (#(child d segB)))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk HΦ
  have hs : lookupH R V (child d tmpB) = none := by
    rw [lookupH_child hr hd V tmpB_ok]; exact hn
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc (L := hG.goose_localGS) R j γ V $$ Hinv Ht with ⟨%ko, Hw, %Hs, Hclose⟩
  imodintro
  iapply wp_osRenameAbsentG d tmpB d segB j j tmpB_ok segB_ok R V _ _ k s qp3
    (lookupH_root hr hd V) (lookupH_root hr hd V) hs bootN_disj $$ Hos Hw Hk
  iintro %e %he Ht'
  imod Hclose $$ %V %Hs Ht' with Ht
  imodintro
  iapply HΦ $$ %e %he Ht

/-- One attempt of `os.Rename(d/seg.tmp, d/seg)`, after the rename logged or not: on `V`, the
rename; on `V` renamed, `seg.tmp` is gone and it fails. -/
theorem wp_renameStep (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (i : Ino) (k s : Nat)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hk : V.now.entry j tmpB = some (.file i))
    (hns : ∀ J, V.now.entry j segB ≠ some (.dir J)) (V1 : Hist)
    (hp : V1 = V ∨ V1 = V.push ⟨renameOp R V j tmpB j d segB (.file i), V.2.length⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V1 -∗ osCall (GF := GF) k s (1 : Qp).half.half -∗
      ghostVar (GF := GF) γ (1 : Qp).half (some i) -∗
      (∀ (e : w64) (V' : Hist),
        ⌜V' = V ∨ V' = V.push ⟨renameOp R V j tmpB j d segB (.file i), V.2.length⟩⌝ -∗
        ⌜e = 0 → V' = V.push ⟨renameOp R V j tmpB j d segB (.file i), V.2.length⟩⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ ghostVar (GF := GF) γ (1 : Qp).half (some i) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d tmpB)) (#(child d segB)))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  rcases hp with rfl | rfl
  · iapply wp_renameTmp R d j γ V1 k s i hr hd hk hns $$ Hos Hinv Ht Hk Hγ
    iintro %e %V' %hp Ht Hγ
    iapply HΦ $$ %e %V' [] [] Ht Hγ
    · ipureintro
      rcases hp with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
      · exact .inr rfl
      · exact .inl rfl
      · exact .inr rfl
    · ipureintro
      intro he; rcases hp with ⟨-, rfl⟩ | ⟨h, -⟩
      · rfl
      · exact absurd he h
  · iapply wp_renameAbsentTmp R d j γ (V.push ⟨renameOp R V j tmpB j d segB (.file i), V.2.length⟩) k s hr hd (tmp_renamed hk) $$ Hos Hinv Ht Hk
    iintro %e %he Ht
    iapply HΦ $$ %e %_ [] [] Ht Hγ
    · ipureintro; exact .inr rfl
    · ipureintro; exact fun h => absurd h he

/-- `os.Rename(d/seg.tmp, d/seg)`, `seg.tmp` the file of the invariant's key `i`, `seg` not a
directory: on success `seg` names `i`. -/
theorem wp_renameSeg (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (i : Ino)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hk : V.now.entry j tmpB = some (.file i))
    (hns : ∀ J, V.now.entry j segB ≠ some (.dir J)) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) R j γ ∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗
        ghostVar (GF := GF) γ (1 : Qp).half (some i) }}
      (App (App (Val (@! os.Rename)) (Val #(child d tmpB))) (Val #(child d segB)))
    {{ (err : GoInterface), RET #err; ghostVar γ (1 : Qp).half (some i) ∗
        ∃ V', osTree (DFrac.own (1 : Qp).half) R V' ∗
          ⌜err = interface.nil → V'.now.entry j segB = some (.file i)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  have hnd : ∀ J, lookupH R V (child d segB) ≠ some (.dir J) := by
    intro J; rw [lookupH_child hr hd V segB_ok]; exact hns J
  have htp : (Hist.st R V).TreePath (child d segB) :=
    .inr (treeName_child (st := Hist.st R V) (lookupH_root hr hd V) segB_ok)
  icases (osTree_halves (1 : Qp).half R V).1 $$ Ht with Ht
  wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
  (try wp_auto)
  wp_apply wp_osLstatDir (child d segB) R V _ _ t _ htp hnd CoPset.subseteq_top $$ Hos Ht Hk
    as %e0 Ht
  icases (osTree_halves (1 : Qp).half R V).2 $$ Ht with Ht
  (try wp_auto)
  let Vr := V.push ⟨renameOp R V j tmpB j d segB (.file i), V.2.length⟩
  have hVr : Vr.now.entry j segB = some (.file i) := seg_renamed hk
  have hVrt : Vr.now.entry j tmpB = none := tmp_renamed hk
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = V := ⟨_, rfl⟩
  ihave Ht : osTree (DFrac.own (1 : Qp).half) R V1 $$ [Ht]
  · subst hV1; iexact Ht
  ihave Hp : ⌜V1 = V ∨ V1 = Vr⌝ $$ []
  · ipureintro; exact .inl hV1
  clear hV1
  iloeb as IH generalizing %V1 Hp Ht Hγ
  icases Hp with %Hp
  icases (osTree_halves (1 : Qp).half R V1).1 $$ Ht with Ht
  wp_apply wp_osCallBegin R V1 _ _ CoPset.subseteq_top $$ Hos Ht as %t1 Ht Hk
  (try wp_auto)
  wp_apply wp_renameStep R d j γ V i t1 _ hr hd hk hns V1 Hp $$ Hos Hinv Ht Hk Hγ
    as %e %V' %hV' %he Ht Hγ
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V' [] Ht Hγ HΦ
    ipureintro; exact hV'
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hγ
    iexists V'
    iframe Ht
    ipureintro; intro _
    rw [he he0]; exact hVr
  rw [decide_eq_false he0]
  wp_auto
  wp_apply wp_errno
  unfold os.model.linkError
  rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
  wp_auto
  iapply HΦ
  iframe Hγ
  iexists V'
  iframe Ht
  ipureintro; intro h; cases h

/-- A directory fd's fraction back, with the rest of the history: the whole. -/
theorem osDir_back (q1 q2 : Qp) (R : Roots) (V : Hist) (j : Ino) (g : DirG) :
    osTree (GF := GF) (DFrac.own q1) R V ∗ osDir (GF := GF) j (DFrac.own q2) g ⊢
      osTree (GF := GF) (DFrac.own (q1 + q2)) R V := by
  unfold osDir
  iintro ⟨H1, %R', %V', H2, -⟩
  icases osTree_agree (L := hG.goose_localGS) _ _ R R' V V' $$ H1 H2 with %h
  obtain ⟨rfl, rfl⟩ := h
  iapply (osTree_split (L := hG.goose_localGS) q1 q2 R V).2
  iframe

/-- `readNames(d)`, `d` the root of `j`, with a fraction of the history: the names of `j` now,
each once, or `ok = false`. -/
theorem wp_readNames (R : Roots) (d : GoString) (j : Ino) (V : Hist) (q : Qp)
    (hr : RootsOk R) (hd : (d, j) ∈ R) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readNames)) (Val #d))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); osTree (DFrac.own q) R V ∗
        (⌜ok = false⌝ ∨ ∃ names : List GoString, ⌜ok = true ∧ names.Nodup ∧
          ∀ b, b ∈ names ↔ (V.now.entry j b).isSome⌝ ∗ sl ↦* names) }} := by
  wp_start as ⟨#Hinv, Ht⟩
  ihave Ht := (osTree_halves q R V).1 $$ Ht
  (try wp_auto)
  wp_apply os.Open.wp_dir d q.half q.half R V j (lookupH_root hr hd V) $$ [Hinv Ht] as %f %err Hr
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Ht, Hfd⟩ | ⟨%herr, Ht⟩)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    ihave Ht := (osTree_halves q R V).2 $$ Ht
    iframe Ht
    ileft; ipureintro; rfl
  subst herr
  (try wp_auto)
  wp_apply os.File.Readdirnames.wp_dir f fd d (DFrac.own 1) j q.half (dview V j) _ (by decide)
    $$ [Hinv Hf Hfd] as %sl %err ⟨Hf, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%names, %hn, Hsl, Hfd⟩ | ⟨%herr, %rs, Hfd⟩)
  · obtain ⟨rfl, hnd, hmem⟩ := hn
    (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (j, .done (dview V j) q.half) $$ [Hinv Hf Hfd] as %e Hd
    · iframe; iexact Hinv
    simp only [rdBack, DirPh.q, DirPh.g] at *
    ihave Ht := osDir_back q.half q.half R V j _ $$ [Ht Hd]
    · iframe
    ihave Ht := (osTree_halves q R V).2 $$ Ht
    (try wp_auto)
    iapply HΦ
    iframe Ht
    iright
    iexists names
    iframe
    ipureintro
    refine ⟨rfl, hnd, fun b => ?_⟩
    rw [hmem b, dview_now, entsOf_lookup]
  · (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (j, .reading rs (dview V j) q.half) $$ [Hinv Hf Hfd]
      as %e Hd
    · iframe; iexact Hinv
    simp only [rdBack, DirPh.q, DirPh.g] at *
    ihave Ht := osDir_back q.half q.half R V j _ $$ [Ht Hd]
    · iframe
    ihave Ht := (osTree_halves q R V).2 $$ Ht
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Ht
    ileft; itrivial

/-- `syncDir(d)`, `d` the root of `j`, with a fraction of the history: any result. -/
theorem wp_syncDir (R : Roots) (d : GoString) (j : Ino) (V : Hist) (q : Qp)
    (hr : RootsOk R) (hd : (d, j) ∈ R) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.syncDir)) (Val #d))
    {{ (ok : Bool), RET #ok; osTree (DFrac.own q) R V }} := by
  wp_start as ⟨#Hinv, Ht⟩
  ihave Ht := (osTree_halves q R V).1 $$ Ht
  (try wp_auto)
  wp_apply os.Open.wp_dir d q.half q.half R V j (lookupH_root hr hd V) $$ [Hinv Ht] as %f %err Hr
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Ht, Hfd⟩ | ⟨%herr, Ht⟩)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iapply (osTree_halves q R V).2
    iexact Ht
  subst herr
  (try wp_auto)
  wp_apply os.File.Sync.wp_dir f fd d (DFrac.own 1) (DFrac.own 1) (j, .idle (dview V j) q.half)
    $$ [Hinv Hf Hfd] as %err ⟨Hf, Hfd⟩
  · iframe; iexact Hinv
  (try wp_auto)
  wp_apply os.File.Close.wp_dir f fd d (j, .idle (dview V j) q.half) $$ [Hinv Hf Hfd] as %e Hd
  · iframe; iexact Hinv
  simp only [rdBack, DirPh.q, DirPh.g] at *
  ihave Ht := osDir_back q.half q.half R V j _ $$ [Ht Hd]
  · iframe
  ihave Ht := (osTree_halves q R V).2 $$ Ht
  cases err with
  | nil => (try wp_auto); iapply HΦ; iframe Ht
  | ok ie => (try wp_auto); iapply HΦ; iframe Ht

end oscalls3

/-! ## The data -/

section data
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]

theorem wp_dataOk (sl : GoSlice) (dq : DFrac) (vs : List w8) (h : vs = dataC) :
    {{ (sl ↦*{dq} vs : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.dataOk)) (Val #sl))
    {{ RET #true; sl ↦*{dq} vs }} := by
  wp_start as Hs
  icases ownSlice_len sl dq vs $$ Hs with %Hlen
  have hl : vs.length = 8 := by rw [h]; rfl
  have hv : ∀ i : Nat, i < 8 → vs[i]? = dataC[i]? := by
    intro i _; rw [h]
  have hs8 : sl.len = W64 8 := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  have hs8' : (8 : Int) ≤ sint.Z sl.len := by rw [hs8]; decide
  try wp_auto
  rw [decide_eq_true hs8]
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) vs dq (W8 0xde) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 0)).toNat = 0 from rfl]; exact hv 0 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 1)) vs dq (W8 0xad) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 1)).toNat = 1 from rfl]; exact hv 1 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z sl.len by
    rw [show sint.Z (W64 2) = 2 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 2)) vs dq (W8 0xbe) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 2)).toNat = 2 from rfl]; exact hv 2 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z sl.len by
    rw [show sint.Z (W64 3) = 3 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 3)) vs dq (W8 0xef) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 3)).toNat = 3 from rfl]; exact hv 3 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) < sint.Z sl.len by
    rw [show sint.Z (W64 4) = 4 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 4)) vs dq (W8 0x01) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 4)).toNat = 4 from rfl]; exact hv 4 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) < sint.Z sl.len by
    rw [show sint.Z (W64 5) = 5 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 5)) vs dq (W8 0x23) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 5)).toNat = 5 from rfl]; exact hv 5 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 6) ∧ sint.Z (W64 6) < sint.Z sl.len by
    rw [show sint.Z (W64 6) = 6 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 6)) vs dq (W8 0x45) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 6)).toNat = 6 from rfl]; exact hv 6 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) < sint.Z sl.len by
    rw [show sint.Z (W64 7) = 7 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 7)) vs dq (W8 0x67) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 7)).toNat = 7 from rfl]; exact hv 7 (by decide)
  try wp_auto
  iapply HΦ
  iframe

theorem wp_newData :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.newData)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* dataC }} := by
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal (V := w8) (l := dataC)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hs, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd]
  (try wp_auto)
  iapply HΦ
  iexact Hs

end data

/-! ## `check`, `commit` and `Boot` -/

/-- What the program knows of the file of `seg`'s key, held at the fractions `m`, `bs`: its first
8 bytes in the page cache are the data. -/
def CheckOk (m : OsMeta) (bs : List ByteG) : Prop :=
  8 ≤ m.size ∧ bs.length = 8 ∧ bs.map Prod.fst = dataC

theorem dataC_length : dataC.length = 8 := rfl

/-- The data written and synced: every crash leaves it. -/
theorem synced_good (m : OsMeta) (hsz : m.size = 8) (ys : List ByteG)
    (hys : ys.map Prod.fst = dataC) :
    ∀ fo, FileCrashedR m.synced [(0, DFrac.own (1 : Qp).half, ys.map (fun x => durB x.1))] fo →
      DataGood fo := by
  intro fo hfc f hf
  subst hf
  obtain ⟨-, hlo, -, -, -⟩ := hfc f rfl
  have hl : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  have h8 : 8 ≤ f.size := by simpa [OsMeta.synced, hsz] using hlo
  refine ⟨h8, fun b hb => ?_⟩
  have hyb : b < ys.length := by omega
  rw [crashed_dur hfc (List.mem_singleton_self _) (b := b) (x := (ys[b]'hyb).1) (Nat.zero_le _)
    (by simpa using hyb) (by simp) (by omega), ← hys, List.getElem?_map,
    List.getElem?_eq_getElem hyb]; rfl

theorem checkOk_synced (m : OsMeta) (hsz : m.size = 8) (ys : List ByteG)
    (hys : ys.map Prod.fst = dataC) : CheckOk m.synced (ys.map (fun x => durB x.1)) := by
  have hl : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  refine ⟨by simp [OsMeta.synced, hsz], by simp [hl], ?_⟩
  simp only [List.map_map]
  rw [← hys]; rfl

theorem newMeta_size : newMeta.size = 0 := rfl

/-- The bytes a whole write of the data leaves in a new file: the data. -/
theorem pwOut_data {ys : List ByteG} (h : os.PwOut newMeta 0 dataC 8 [] ys) :
    ys.map Prod.fst = dataC := by
  obtain ⟨hl, hv⟩ := h
  have hl8 : ys.length = 8 := by rw [hl, newMeta_size]; rfl
  apply List.ext_getElem (by simp [hl8, dataC])
  intro i h1 h2
  simp only [List.getElem_map]
  rw [(hv i (by simpa using h1)).1]
  have hi : i < 8 := by simpa [hl8] using h1
  simp only [pwByte, Nat.zero_add, if_pos hi, Nat.sub_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < dataC.length from hi), Option.getD_some]

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- `check(d)`, `seg` the file `i`, with half of its `OsMeta` and of its first 8 bytes, the data:
it does not panic. -/
theorem wp_check (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (R : Roots) (d : GoString) (j : Ino) (V : Hist) (q : Qp) (hr : RootsOk R) (hd : (d, j) ∈ R)
    (i : Ino) (hk : V.now.entry j segB = some (.file i))
    (m : OsMeta) (bs : List ByteG) (hok : CheckOk m bs) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V ∗
        osMeta (GF := GF) i (DFrac.own (1 : Qp).half) m ∗
        osBytes (GF := GF) i 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.check)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, Ht, Hm, Hb⟩
  wp_auto
  rw [show d ++ go!"/seg" = child d segB from rfl]
  have hl : lookupH R V (child d segB) = some (.file i) := by
    rw [lookupH_child hr hd V segB_ok]; exact hk
  wp_apply os.OpenFile.wp_nsRO (child d segB) (W32 0) q R V i hl $$ [Hos Ht]
    as %f %err ⟨Ht, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | %herr)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  subst herr
  obtain ⟨hsz, hbl, hbv⟩ := hok
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  have h8 : sint.nat (W64 8) = 8 := rfl
  wp_apply wp_ReadAt f fd (child d segB) (DFrac.own 1) buf
      (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0) (DFrac.own 1)
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨i, true, false⟩ m bs rfl (by decide)
      (by rw [List.length_replicate, h8]; decide) (by rw [List.length_replicate, h8]; decide)
      (by rw [List.length_replicate, h8]; simp; omega)
      (by rw [List.length_replicate, h8]; exact hbl) $$ [Hos Hf Hbuf Hfd Hm Hb]
    as %n %err ⟨Hf, Hfd, Hm, Hb, %vs', Hbuf, %Hres⟩
  · iframe; iexact Hos
  (try wp_auto)
  wp_apply wp_Close f fd (child d segB) ⟨i, true, false⟩ $$ [Hos Hf Hfd] as %e -
  · iframe; iexact Hos
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | hne⟩ := Hres
  · (try wp_auto)
    wp_apply wp_dataOk buf (DFrac.own 1) vs' (by rw [hvs', hbv]) $$ [Hbuf] as Hbuf
    · iframe
    (try wp_auto)
    iapply HΦ
    itrivial
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial

/-- `commit(d)`, nothing at `seg.tmp` or `seg` now: it does not panic. -/
theorem wp_commit (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino)
    (hr : RootsOk R) (hd : (d, j) ∈ R)
    (hn : V.now.entry j tmpB = none) (hs : V.now.entry j segB = none) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗ ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.commit)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  wp_auto
  rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl, show (W64 2 ||| W64 64) = W64 66 from by decide]
  wp_apply wp_openTmp R d j γ V hr hd hn (W32 438) $$ [Hos Hinv Ht] as %f %err Hr
  · iframe; iframe #
  icases Hr with (⟨%fd, %i, %hek, Hf, Hfd, Hm, Ht⟩ | ⟨%herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  subst hek
  generalize hV2 : V.push ⟨.create j tmpB i, V.2.length⟩ = V2
  have hk2 : V2.now.entry j tmpB = some (.file i) := by rw [← hV2]; exact tmp_created
  have hs2 : V2.now.entry j segB = none := by rw [← hV2, seg_created]; exact hs
  (try wp_auto)
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  ihave Hb0 : osBytes i (W64 0).toNat (DFrac.own 1) [] $$ []
  · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
  ihave Hmc : mcellsAny newMeta.maps (W64 0).toNat ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny; simp only [newMeta, initMeta]; iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_WriteAt f fd (child d tmpB) (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0) (DFrac.own 1)
      ⟨i, true, true⟩ newMeta [] rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) $$ [Hos Hf Hsl Hfd Hm Hb0 Hmc]
    as %n %err ⟨Hf, Hsl, Hfd, %k, %ys, %Hres, Hm, Hys, -⟩
  · iframe; iexact Hos
  obtain ⟨hj, hys, -, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d tmpB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  have hys' : ys.map Prod.fst = dataC := pwOut_data hys
  have hysl : ys.length = (pwPost newMeta (W64 0).toNat dataC.length dataC.length).size := by
    rw [hys.1]; rfl
  (try wp_auto)
  -- `fdatasync`
  wp_apply wp_Fd f fd (child d tmpB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd (DFrac.own 1) ⟨i, true, true⟩ _ 0 ys (OsMeta.covers_whole _ hysl)
      $$ [Hos Hfd Hm Hys]
    as %e ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm, Hys⟩ | ⟨%he, -, -⟩)
  rotate_left
  · rw [show errnoErr e = interface.mkOk syscall.Errno.ty #e from if_neg he.1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child d tmpB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  subst he
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply wp_Close f fd (child d tmpB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; iexact Hos
  (try wp_auto)
  -- the file, durable, goes into the invariant under the key `i`
  icases (osMeta_halves (L := hG.goose_localGS) i _).1 $$ Hm with ⟨Hm, Hmi⟩
  icases (osBytes_halves (L := hG.goose_localGS) i 0 _).1 $$ Hys with ⟨Hys, Hysi⟩
  iapply fupd_wp
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V', %ko', >Ht', >Hv, >%Hp, >Hk⟩
  icases osTree_agree (L := hG.goose_localGS) _ _ R R V2 V' $$ Ht Ht' with %heq
  obtain ⟨-, rfl⟩ := heq
  imod ghostVar_update_halves (some i) γ _ _ $$ Hγ Hv with ⟨Hγ, Hv⟩
  imod Hclose $$ [Ht' Hv Hmi Hysi] with -
  · inext
    iexists V2, (some i)
    iframe Ht' Hv
    isplitr
    · ipureintro; exact ⟨safeH_rekey Hp.1 (segNoneH_of Hp.2 hs2), Hp.2⟩
    unfold keyRes
    iexists _, _
    iframe Hmi Hysi
    ipureintro; exact synced_good _ rfl ys hys'
  imodintro
  -- the rename
  try rw [show d ++ go!"/seg" = child d segB from rfl]
  try rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl]
  wp_apply wp_renameSeg R d j γ V2 i hr hd hk2 (fun J => by rw [hs2]; simp) $$ [Hos Ht Hγ]
    as %err ⟨Hγ, %V3, Ht, %hV3⟩
  · iframe; unfold bootInv; iframe #
  cases err with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  have hk3 := hV3 rfl
  (try wp_auto)
  -- the directory's sync
  wp_apply wp_syncDir R d j V3 _ hr hd $$ [Hos Ht] as %ok Ht
  · iframe; iexact Hos
  cases ok with
  | false =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | true =>
  (try wp_auto)
  wp_apply wp_check wp_ReadAt wp_Close R d j V3 _ hr hd i hk3 _ _
      (checkOk_synced (pwPost newMeta (W64 0).toNat dataC.length dataC.length) rfl ys hys')
      $$ [Hos Ht Hm Hys]
  · iframe; iexact Hos
  (try wp_auto)
  iapply HΦ
  itrivial

/-- The program's half of the file of `seg`'s key `ko`, as `check` needs it. -/
def segRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List ByteG),
      osMeta (GF := GF) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (GF := GF) k 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜CheckOk m bs⌝)

/-- `Boot(d)`, `d` the root of `j`, from the history `V0` whose `seg` and `seg.tmp` are as the
invariant's key `ko0` says: it does not panic. -/
theorem wp_Boot (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (d : GoString) (j : Ino) (γ : GName) (V0 : Hist) (ko0 : Option Ino)
    (hr : RootsOk R) (hd : (d, j) ∈ R) (hso : SafeT j ko0 V0.now) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V0 ∗
        ghostVar (GF := GF) γ (1 : Qp).half ko0 ∗ segRes ko0 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ, Hs⟩
  wp_auto
  wp_apply wp_readNames R d j V0 _ hr hd $$ [Hos Ht] as %sl %ok ⟨Ht, Hr⟩
  · iframe; iexact Hos
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hnodup, hmem⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString) (hv : Bool) (V : Hist),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗ "Hhv" ∷ have_ptr ↦ hv ∗
      "Ht" ∷ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧
        hv = decide (segB ∈ names.take (sint.nat i)) ∧
        V.now.entry j segB = V0.now.entry j segB ∧
        (tmpB ∈ names.take (sint.nat i) → V.now.entry j tmpB = none) ∧
        (tmpB ∉ names.take (sint.nat i) → V = V0)⌝) $$ [i n «have» Ht]
  · iexists W64 0, _, false, V0
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_, rfl, ?_, fun _ => rfl⟩ <;>
      rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hhv, hseg, htmp, hsame⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat i < names.length := by word
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨b, hb⟩ : ∃ b, names[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z i) names (DFrac.own 1) b hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hb
    have htake : names.take (sint.nat (i + W64 1)) = names.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [List.take_add_one, hb]; rfl
    (try wp_auto)
    have hbt0 : b ∉ names.take (sint.nat i) := not_mem_take_of_nodup hnodup hb
    by_cases hbs : b = segB
    · subst hbs
      rw [decide_eq_true (show segB = go!"seg" from rfl)]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, segB, true, V
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, hseg, ?_, ?_⟩
      · rw [htake]; simp
      · rw [htake]; intro h
        simp only [List.mem_append, List.mem_singleton, tmp_ne_seg, or_false] at h
        exact htmp h
      · rw [htake]; intro h
        simp only [List.mem_append, List.mem_singleton, tmp_ne_seg, or_false] at h
        exact hsame h
    rw [decide_eq_false (show ¬ b = go!"seg" from hbs)]
    wp_auto
    by_cases hbt : b = tmpB
    · subst hbt
      rw [decide_eq_true (show tmpB = go!"seg.tmp" from rfl)]
      wp_auto
      rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl]
      wp_apply wp_removeTmp R d j γ V hr hd $$ [Hos Hinv Ht] as %err ⟨%V', Ht, %hV'⟩
      · iframe; iframe #
      cases err with
      | ok ie =>
        (try wp_auto)
        wp_for_post
        iapply HΦ
        itrivial
      | nil =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1, tmpB, hv, V'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, hV'.1.trans hseg, fun _ => hV'.2 rfl, ?_⟩
      · rw [htake, hhv]; simp [tmp_ne_seg, Ne.symm tmp_ne_seg]
      · rw [htake]; simp
    rw [decide_eq_false (show ¬ b = go!"seg.tmp" from hbt)]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, b, hv, V
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, hseg, ?_, ?_⟩
    · rw [htake, hhv]; simp [Ne.symm hbs]
    · rw [htake]; intro h; simp [Ne.symm hbt] at h; exact htmp h
    · rw [htake]; intro h; simp [Ne.symm hbt] at h; exact hsame h
  · -- the loop is done
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hhv htmp hsame
    subst hhv
    by_cases hsin : segB ∈ names
    · rw [decide_eq_true hsin]
      (try wp_auto)
      obtain ⟨x, hx⟩ : ∃ x, V0.now.entry j segB = some x := by
        have := (hmem segB).1 hsin
        cases h : V0.now.entry j segB with
        | none => rw [h] at this; cases this
        | some x => exact ⟨x, rfl⟩
      obtain ⟨-, -, hn | ⟨k, rfl, hk⟩⟩ := hso
      · rw [hn] at hx; cases hx
      unfold segRes
      icases Hs with ⟨%m, %bs, Hm, Hb, %hok⟩
      wp_apply wp_check wp_ReadAt wp_Close R d j V _ hr hd k (by rw [hseg]; exact hk) m bs hok
        $$ [Hos Ht Hm Hb]
      · iframe; iexact Hos
      (try wp_auto)
      iapply HΦ
      itrivial
    · rw [decide_eq_false hsin]
      (try wp_auto)
      have hs0 : V0.now.entry j segB = none := by
        cases h : V0.now.entry j segB with
        | none => rfl
        | some x => exact absurd ((hmem segB).2 (by rw [h]; rfl)) hsin
      have hn : V.now.entry j tmpB = none := by
        by_cases ht : tmpB ∈ names
        · exact htmp ht
        · rw [hsame ht]
          cases h : V0.now.entry j tmpB with
          | none => rfl
          | some x => exact absurd ((hmem tmpB).2 (by rw [h]; rfl)) ht
      wp_apply wp_commit wp_ReadAt wp_Close wp_WriteAt wp_Fd wp_Fdatasync R d j γ V ko0 hr hd hn
          (hseg.trans hs0) $$ [Hos Hinv Ht Hγ]
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial

end prog
end osfs_walfs
end EtcdGrove
end Perennial

end
