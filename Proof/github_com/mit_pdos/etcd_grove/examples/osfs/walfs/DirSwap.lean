/-
The proofs of `examples/osfs/walfs`'s `dirswap.go` (one generation), over the file extension v2:
the crash invariant of the root `dir` (of inode `j`), and the specs of `Create`, `checkDir` and
`BootDir`.

The invariant (`dsInv`) holds half of the tree's history (`osTree`) and says of every crash of it
(`SafeH`, through `TreeCrashed`: a prefix of the logged operations replayed, or all of them when
only the process restarts): `wal` is no file, and if it is a directory, its `seg` is the file of
the key `ko`, a ghost variable whose other half the program keeps, with half of that file's
`OsMeta` and bytes, every crash of which leaves the data (`keyRes`, `DSCheck.lean`). It also says
that once `wal` is in a crash of the history, it and its `seg` are as now (`MonoH`): the program
changes the tree only while `wal` is absent, and makes `wal` appear only by renaming `wal.tmp`
onto it. The program keeps the other half of the history, and opens the invariant around each call
that changes the tree (`unlink`, `rmdir`, `mkdir`, `open(O_CREAT)`, `rename`). Before the rename
`Create` deposits the new `seg`'s file under the key, which it may change, `wal` being absent from
every crash (`MonoH`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSCheck
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSTree
public import Spec.os.File__Sync
public import Spec.os.File__WriteAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

/-! ## The names -/

def walB : GoString := go!"wal"
def wtB : GoString := go!"wal.tmp"

theorem walB_ok : NameOk walB := by decide
theorem wtB_ok : NameOk wtB := by decide
theorem wt_ne_wal : wtB ≠ walB := by decide
theorem seg_ne_wal : segB ≠ walB := by decide
theorem seg_ne_wt : segB ≠ wtB := by decide

/-! ## The tree's entries after an operation -/

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

theorem entry_mkdir (m : Tree) (j : Ino) (x : GoString) (J : Ino) (j' : Ino) (y : GoString) :
    ((MetaOp.mkdir j x J).apply m).entry j' y =
      if J = j' then none else if j = j' ∧ x = y then some (.dir J) else m.entry j' y := by
  simp only [MetaOp.apply]
  rw [← entsOf_lookup]
  by_cases hJ : J = j'
  · subst hJ; rw [entsOf_insert_eq, if_pos rfl]; rfl
  · rw [entsOf_insert_ne _ _ hJ, entsOf_lookup, entry_upd, if_neg hJ]
    by_cases hj : j = j'
    · subst hj; by_cases hx : x = y
      · subst hx; simp
      · simp [hx, ← entsOf_lookup]
    · simp [hj]

/-- A rename within the directory `j` of the entry `x`, naming `n`, to `y`. -/
theorem entry_rename (m : Tree) (j : Ino) (x y : GoString) (n : Node) (old : Option Node)
    (hn : m.entry j x = some n) (_hxy : x ≠ y) (j' : Ino) (z : GoString) :
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

/-- The operation `o` leaves `wal` absent. -/
def WalKeep (j : Ino) (o : MetaOp) : Prop :=
  ∀ m : Tree, m.entry j walB = none → (o.apply m).entry j walB = none

theorem walKeep_remove (j J : Ino) (b : GoString) (n : Node) (hb : b ≠ walB) :
    WalKeep j (.remove J b n) := by
  intro m hm; rw [entry_remove, if_neg (fun h => hb h.2)]; exact hm

theorem walKeep_create (j J : Ino) (b : GoString) (i : Ino) (hb : b ≠ walB) :
    WalKeep j (.create J b i) := by
  intro m hm; rw [entry_create, if_neg (fun h => hb h.2)]; exact hm

theorem walKeep_mkdir (j j' : Ino) (b : GoString) (J : Ino) (hb : b ≠ walB) :
    WalKeep j (.mkdir j' b J) := by
  intro m hm; rw [entry_mkdir]; split
  · rfl
  · rw [if_neg (fun h => hb h.2)]; exact hm

/-! ## What every crash must be -/

/-- **The tree a boot may find**, in the directory `j`: `wal` no file; if `wal` is a directory, its
`seg` the file of the key `ko`. -/
def SafeT (j : Ino) (ko : Option Ino) (m : Tree) : Prop :=
  (∀ i, m.entry j walB ≠ some (.file i)) ∧
  (∀ J, m.entry j walB = some (.dir J) → ∃ k, ko = some k ∧ m.entry J segB = some (.file k))

/-- Every crash of the history `V` is `SafeT`. -/
def SafeH (j : Ino) (ko : Option Ino) (V : Hist) : Prop := ∀ V', TreeCrashed V V' → SafeT j ko V'.now

/-- Once `wal` is in a crash of `V`, it is as in `V` now, and so is its `seg`. -/
def MonoH (j : Ino) (V : Hist) : Prop :=
  ∀ V', TreeCrashed V V' → V'.now.entry j walB ≠ none →
    V'.now.entry j walB = V.now.entry j walB ∧
    ∀ J, V.now.entry j walB = some (.dir J) → V'.now.entry J segB = V.now.entry J segB

theorem safeH_now {j : Ino} {ko : Option Ino} {V : Hist} (h : SafeH j ko V) : SafeT j ko V.now :=
  h (V.now, []) (treeCrashed_refl V)

theorem safeT_none {j : Ino} {ko : Option Ino} {m : Tree} (h : m.entry j walB = none) :
    SafeT j ko m :=
  ⟨fun i => by rw [h]; simp, fun J hJ => by rw [h] at hJ; cases hJ⟩

/-- With `wal` absent now, it is absent from every crash. -/
theorem wal_none_all {j : Ino} {V : Hist} (hm : MonoH j V) (hw : V.now.entry j walB = none) :
    ∀ V', TreeCrashed V V' → V'.now.entry j walB = none := by
  intro V' hc
  by_cases hne : V'.now.entry j walB = none
  · exact hne
  · exact absurd ((hm V' hc hne).1.trans hw) hne

/-- An operation logged while `wal` is absent, leaving a `SafeT` tree. -/
theorem inv_push {j : Ino} {ko : Option Ino} {V : Hist} (h : SafeH j ko V ∧ MonoH j V)
    (hw : V.now.entry j walB = none) (e : LogEntry) (he : SafeT j ko (e.op.apply V.now)) :
    SafeH j ko (V.push e) ∧ MonoH j (V.push e) := by
  refine ⟨fun V' hc => ?_, fun V' hc hne => ?_⟩
  · rcases treeCrashed_push hc with hc | hn
    · exact h.1 V' hc
    · rw [hn, Hist.push_now]; exact he
  · rcases treeCrashed_push hc with hc | hn
    · exact absurd (wal_none_all h.2 hw V' hc) hne
    · exact ⟨by rw [hn], fun J _ => by rw [hn]⟩

/-- The history after a call that may have logged an operation leaving `wal` absent. -/
def KeepW (j : Ino) (V V' : Hist) : Prop :=
  V' = V ∨ ∃ o, V' = V.push ⟨o, V.2.length⟩ ∧ WalKeep j o

theorem keep_wal {j : Ino} {V V' : Hist} (hw : V.now.entry j walB = none) (hk : KeepW j V V') :
    V'.now.entry j walB = none := by
  rcases hk with rfl | ⟨o, rfl, ho⟩
  · exact hw
  · rw [Hist.push_now]; exact ho _ hw

theorem inv_keep {j : Ino} {ko : Option Ino} {V V' : Hist} (h : SafeH j ko V ∧ MonoH j V)
    (hw : V.now.entry j walB = none) (hk : KeepW j V V') : SafeH j ko V' ∧ MonoH j V' := by
  rcases hk with rfl | ⟨o, rfl, ho⟩
  · exact h
  · exact inv_push h hw _ (safeT_none (ho _ hw))

/-- With `wal` absent now, the key does not matter. -/
theorem inv_rekey {j : Ino} {ko : Option Ino} {V : Hist} (h : SafeH j ko V ∧ MonoH j V)
    (hw : V.now.entry j walB = none) (ko' : Option Ino) : SafeH j ko' V ∧ MonoH j V :=
  ⟨fun V' hc => safeT_none (wal_none_all h.2 hw V' hc), h.2⟩

/-- With the key's file named nowhere now, no crash has `wal`: the key `none` will do. -/
theorem inv_unnamed {j k : Ino} {V : Hist} (h : SafeH j (some k) V ∧ MonoH j V)
    (hn : ¬ Named V.now k) : SafeH j none V ∧ MonoH j V := by
  refine ⟨fun V' hc => ?_, h.2⟩
  obtain ⟨h1, h2⟩ := h.1 V' hc
  refine ⟨h1, fun J hJ => ?_⟩
  obtain ⟨k', hk', hs⟩ := h2 J hJ
  cases hk'
  obtain ⟨hm1, hm2⟩ := h.2 V' hc (by rw [hJ]; simp)
  have hW : V.now.entry j walB = some (.dir J) := hm1 ▸ hJ
  exact absurd ⟨J, segB, by rw [← hm2 J hW]; exact hs⟩ hn

/-- A crash of a crash is a crash. -/
theorem treeCrashed_trans {V V' V'' : Hist} (h1 : TreeCrashed V V') (h2 : TreeCrashed V' V'') :
    TreeCrashed V V'' := Fs.treeCrashed_trans h1 h2

/-- The invariant's facts of a crash. -/
theorem inv_crash {j : Ino} {ko : Option Ino} {V V' : Hist} (h : SafeH j ko V ∧ MonoH j V)
    (hc : TreeCrashed V V') : SafeH j ko V' ∧ MonoH j V' := by
  refine ⟨fun V'' hc' => h.1 V'' (treeCrashed_trans hc hc'), ?_⟩
  obtain ⟨n, hn, rfl⟩ := hc
  intro V'' hc' _
  obtain ⟨n', hn', rfl⟩ := hc'
  refine ⟨?_, fun _ _ => ?_⟩ <;> simp [replay, Hist.now]

/-- A history with nothing logged: its only crash is itself. -/
theorem inv_nil {j : Ino} {ko : Option Ino} {t : Tree} (h : SafeT j ko t) :
    SafeH j ko (t, []) ∧ MonoH j (t, []) := by
  refine ⟨fun V' hc => ?_, fun V' hc _ => ?_⟩
  · obtain ⟨n, -, rfl⟩ := hc
    simpa [replay, Hist.now, Hist.ops] using h
  · obtain ⟨n, -, rfl⟩ := hc
    refine ⟨?_, fun _ _ => ?_⟩ <;> simp [replay, Hist.now]

/-! ## The invariant -/

def dsN : Namespace := nroot .@ "dirswap"

theorem dsN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑dsN := mask_ndot_ne' nroot "osfs" "dirswap" (by decide)

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **The crash invariant** of the root of inode `j` (in the roots `R`). -/
def dsInv (R : Roots) (j : Ino) (γ : GName) : IProp GF :=
  inv dsN iprop(∃ (V : Hist) (ko : Option Ino),
    osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ghostVar γ (1 : Qp).half ko ∗
    ⌜SafeH j ko V ∧ MonoH j V⌝ ∗ keyRes (L := L) ko)

instance dsInv_persistent (R : Roots) (j : Ino) (γ : GName) : Persistent (dsInv (L := L) R j γ) := by
  unfold dsInv; infer_instance

/-- The invariant opened around a step, with the caller's quarter of the history and half of the
key: the invariant's half with it, and what closes it again with a history whose facts hold. -/
theorem ds_acc (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino) :
    ⊢ dsInv (L := L) R j γ -∗ osTree (L := L) (DFrac.own (1 : Qp).half.half) R V -∗
      ghostVar γ (1 : Qp).half ko ={⊤, ⊤ \ ↑dsN}=∗
      osTree (L := L) (DFrac.own ((1 : Qp).half.half + (1 : Qp).half)) R V ∗
        ⌜SafeH j ko V ∧ MonoH j V⌝ ∗ ghostVar γ (1 : Qp).half ko ∗
        (∀ V', ⌜SafeH j ko V' ∧ MonoH j V'⌝ -∗ osTree (L := L) (DFrac.own 1) R V' ={⊤ \ ↑dsN, ⊤}=∗
          osTree (L := L) (DFrac.own (1 : Qp).half) R V') := by
  iintro #Hinv Ht Hγ
  unfold dsInv
  imod inv_acc (E := ⊤) (show ↑dsN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko1, >Ht1, >Hv, >%Hs, >Hk⟩
  icases tree_combine _ _ R R V V1 $$ Ht Ht1 with ⟨%he, Ht⟩
  obtain ⟨-, rfl⟩ := he
  icases ghostVar_agree γ ko _ ko1 _ $$ Hγ Hv with %hko
  subst hko
  imodintro
  iframe Ht Hγ
  isplitr
  · ipureintro; exact Hs
  iintro %V' %Hs' Ht'
  icases (tree_halves 1 R V').1 $$ Ht' with ⟨Ht1, Ht2⟩
  imod Hclose $$ [Ht1 Hv Hk] with -
  · inext; iexists V', ko; iframe; ipureintro; exact Hs'
  imodintro
  iexact Ht2

/-- With `wal` absent now, a new key and its file deposited. -/
theorem ds_deposit (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino) (k : Ino)
    (hw : V.now.entry j walB = none) :
    ⊢ dsInv (L := L) R j γ -∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗
      ghostVar γ (1 : Qp).half ko -∗ keyRes (L := L) (some k) ={⊤}=∗
      osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ghostVar γ (1 : Qp).half (some k) := by
  iintro #Hinv Ht Hγ Hk
  unfold dsInv
  imod inv_acc (E := ⊤) (show ↑dsN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko1, >Ht1, >Hv, >%Hs, >-⟩
  icases tree_agree _ _ R R V V1 $$ Ht Ht1 with %he
  obtain ⟨-, rfl⟩ := he
  imod ghostVar_update_halves (some k) γ _ _ $$ Hγ Hv with ⟨Hγ, Hv⟩
  imod Hclose $$ [Ht1 Hv Hk] with -
  · inext; iexists V, (some k); iframe; ipureintro; exact inv_rekey Hs hw _
  imodintro
  iframe

end res

/-! ## The calls that change the tree, with the invariant -/

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- A metadata step by the call `k`, whose spec's postcondition is `P`, the invariant opened
around it, `P` keeping the invariant's facts. -/
theorem wp_dsStep (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino) (k s : Nat)
    (op : String) (v : val) (P : w64 → Hist → Prop)
    (hspec : ∀ Φ' : val → IProp GF, ⊢ osInv (GF := GF) -∗
      osTree (GF := GF) (DFrac.own ((1 : Qp).half.half + (1 : Qp).half)) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ (e : w64) (V' : Hist), ⌜P e V'⌝ -∗ osTree (GF := GF) (DFrac.own 1) R V' -∗ Φ' (#e)) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ ((⊤ : CoPset) \ ↑dsN) {{ Φ' }})
    (hpres : ∀ e V', SafeH j ko V ∧ MonoH j V → P e V' → SafeH j ko V' ∧ MonoH j V')
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half ko -∗
      (∀ (e : w64) (V' : Hist), ⌜P e V'⌝ -∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗
        ghostVar (GF := GF) γ (1 : Qp).half ko -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name op (Val v)) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑dsN))
  imod ds_acc R j γ V ko $$ Hinv Ht Hγ with ⟨Ht, %Hs, Hγ, Hclose⟩
  imodintro
  iapply hspec $$ Hos Ht Hk
  iintro %e %V' %hp Ht
  imod Hclose $$ %V' %(hpres e V' Hs hp) Ht with Ht
  imodintro
  iapply HΦ $$ %e %V' %hp Ht Hγ

/-- `unlink(2)` of `d/b`, a name below a root, `b` not `wal`, `wal` absent: it stays absent. -/
theorem wp_dsUnlink (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino)
    (hw : V.now.entry j walB = none) (d b : GoString) (hb : NameOk b) (hbw : b ≠ walB)
    (hn : ∃ rj ∈ R, CanonBelow rj.1 (child d b)) (k s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half ko -∗
      (∀ (e : w64) (V' : Hist), ⌜V'.now.entry j walB = none⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗
        ghostVar (GF := GF) γ (1 : Qp).half ko -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  by_cases hdd : ∃ J, lookupH R V d = some (.dir J)
  · obtain ⟨J, hd⟩ := hdd
    have hkeep : ∀ e V', UnlinkPost R V d b J e V' → KeepW j V V' := by
      intro e V' hp
      rcases hp with ⟨i, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩
      · exact .inr ⟨_, rfl, walKeep_remove j J b _ hbw⟩
      · exact .inl rfl
      · exact .inr ⟨_, rfl, walKeep_remove j J b _ hbw⟩
      · exact .inl rfl
    iapply wp_dsStep R j γ V ko k s "Unlink" _ (UnlinkPost R V d b J)
      (fun Φ' => wp_osUnlinkG d b J hb R V _ _ k s q_meta hd dsN_disj Φ')
      (fun e V' h hp => inv_keep h hw (hkeep e V' hp)) $$ Hos Hinv Ht Hk Hγ
    iintro %e %V' %hp Ht Hγ
    iapply HΦ $$ %e %V' %(keep_wal hw (hkeep e V' hp)) Ht Hγ
  · have hd : ∀ J, lookupH R V d ≠ some (.dir J) := fun J h => hdd ⟨J, h⟩
    iapply wp_dsStep R j γ V ko k s "Unlink" _ (fun e V' => e ≠ 0 ∧ V' = V)
      (fun Φ' => wp_osUnlinkNoDir d b hb R V _ _ k s q_meta hn hd dsN_disj Φ')
      (fun e V' h hp => by rw [hp.2]; exact h) $$ Hos Hinv Ht Hk Hγ
    iintro %e %V' %hp Ht Hγ
    iapply HΦ $$ %e %V' %(by rw [hp.2]; exact hw) Ht Hγ

/-- `rmdir(2)` of `d/b`, a name below a root, `b` not `wal`, `wal` absent: it stays absent. -/
theorem wp_dsRmdir (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino)
    (hw : V.now.entry j walB = none) (d b : GoString) (hb : NameOk b) (hbw : b ≠ walB)
    (hn : ∃ rj ∈ R, CanonBelow rj.1 (child d b)) (k s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half ko -∗
      (∀ (e : w64) (V' : Hist), ⌜V'.now.entry j walB = none⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗
        ghostVar (GF := GF) γ (1 : Qp).half ko -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  by_cases hdd : ∃ J, lookupH R V d = some (.dir J)
  · obtain ⟨J, hd⟩ := hdd
    have hkeep : ∀ e V', RmdirPost R V d b J e V' → KeepW j V V' := by
      intro e V' hp
      rcases hp with ⟨J', -, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩
      · exact .inr ⟨_, rfl, walKeep_remove j J b _ hbw⟩
      · exact .inl rfl
      · exact .inr ⟨_, rfl, walKeep_remove j J b _ hbw⟩
      · exact .inl rfl
    iapply wp_dsStep R j γ V ko k s "Rmdir" _ (RmdirPost R V d b J)
      (fun Φ' => wp_osRmdirG d b J hb R V _ _ k s q_meta hd dsN_disj Φ')
      (fun e V' h hp => inv_keep h hw (hkeep e V' hp)) $$ Hos Hinv Ht Hk Hγ
    iintro %e %V' %hp Ht Hγ
    iapply HΦ $$ %e %V' %(keep_wal hw (hkeep e V' hp)) Ht Hγ
  · have hd : ∀ J, lookupH R V d ≠ some (.dir J) := fun J h => hdd ⟨J, h⟩
    iapply wp_dsStep R j γ V ko k s "Rmdir" _ (fun e V' => e ≠ 0 ∧ V' = V)
      (fun Φ' => wp_osRmdirNoDir d b hb R V _ _ k s q_meta hn hd dsN_disj Φ')
      (fun e V' h hp => by rw [hp.2]; exact h) $$ Hos Hinv Ht Hk Hγ
    iintro %e %V' %hp Ht Hγ
    iapply HΦ $$ %e %V' %(by rw [hp.2]; exact hw) Ht Hγ

/-- `mkdir(2)` of `dir/wal.tmp`, `dir` the root of `j`, `wal` absent: it stays absent. -/
theorem wp_dsMkdir (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (γ : GName) (V : Hist) (ko : Option Ino) (hw : V.now.entry j walB = none) (k s : Nat)
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half ko -∗
      (∀ (e : w64) (V' : Hist), ⌜MkdirPost R V dir wtB j e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗
        ghostVar (GF := GF) γ (1 : Qp).half ko -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Mkdir" (Val (PairV (osTokV k) (#(child dir wtB))))) {{ Φ }} := by
  have hkeep : ∀ e V', MkdirPost R V dir wtB j e V' → KeepW j V V' := by
    intro e V' hp
    rcases hp with ⟨-, J, -, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩
    · exact .inr ⟨_, rfl, walKeep_mkdir j j wtB J wt_ne_wal⟩
    · exact .inl rfl
    · exact .inr ⟨_, rfl, walKeep_mkdir j j wtB J wt_ne_wal⟩
    · exact .inl rfl
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  iapply wp_dsStep R j γ V ko k s "Mkdir" _ (MkdirPost R V dir wtB j)
    (fun Φ' => wp_osMkdirG dir wtB j wtB_ok R V _ _ k s q_meta (lookupH_root hR hrj V) dsN_disj Φ')
    (fun e V' h hp => inv_keep h hw (hkeep e V' hp)) $$ Hos Hinv Ht Hk Hγ HΦ

/-- `open(2)` with `O_RDWR | O_CREAT` of `d/seg`, `d` the directory `J`, `seg` absent, `wal`
absent: on success a new file of a fresh inode `i`. -/
theorem wp_dsCreate (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino)
    (hw : V.now.entry j walB = none) (d : GoString) (J : Ino) (hd : lookupH R V d = some (.dir J))
    (hn : lookupH R V (child d segB) = none) (k s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half ko -∗
      (∀ fd : w64, ∀ e : w64, ghostVar (GF := GF) γ (1 : Qp).half ko -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ i,
            osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create J segB i, V.2.length⟩) ∗
            osMeta (GF := GF) i (DFrac.own 1) newMeta ∗ osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∨ ∃ i,
            osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create J segB i, V.2.length⟩) ∗
            osMeta (GF := GF) i (DFrac.own 1) newMeta))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open"
        (Val (PairV (osTokV k) (PairV (#(child d segB)) (#flCreat))))) {{ Φ }} := by
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑dsN))
  imod ds_acc R j γ V ko $$ Hinv Ht Hγ with ⟨Ht, %Hs, Hγ, Hclose⟩
  imodintro
  have hpush : ∀ i, SafeH j ko (V.push ⟨.create J segB i, V.2.length⟩) ∧
      MonoH j (V.push ⟨.create J segB i, V.2.length⟩) :=
    fun i => inv_keep Hs hw (.inr ⟨_, rfl, walKeep_create j J segB i seg_ne_wal⟩)
  iapply wp_osOpenCreate d segB R V _ _ k s J segB_ok hd hn q_meta dsN_disj $$ Hos Ht Hk
  iintro %fd %e %- Hr
  icases Hr with (⟨%he, %i, Ht, Hm, Hfd⟩ | ⟨%he, (Ht | ⟨%i, Ht, Hm⟩)⟩)
  · imod Hclose $$ %_ %(hpush i) Ht with Ht
    imodintro
    iapply HΦ $$ %fd %e Hγ
    ileft
    isplitr
    · ipureintro; exact he
    iexists i
    iframe
  · imod Hclose $$ %_ %Hs Ht with Ht
    imodintro
    iapply HΦ $$ %fd %e Hγ
    iright
    isplitr
    · ipureintro; exact he
    ileft; iexact Ht
  · imod Hclose $$ %_ %(hpush i) Ht with Ht
    imodintro
    iapply HΦ $$ %fd %e Hγ
    iright
    isplitr
    · ipureintro; exact he
    iright
    iexists i
    iframe

/-- The rename of `wal.tmp` (the directory `J`, in which `seg` is the file of the key `k`) onto
`wal`, absent: `SafeT` with the key `k`. -/
theorem safeT_rename {j J k : Ino} {m : Tree} (ht : m.entry j wtB = some (.dir J))
    (hs : m.entry J segB = some (.file k)) :
    SafeT j (some k) ((MetaOp.rename j wtB j walB (.dir J) none).apply m) := by
  have hW := entry_rename m j wtB walB (.dir J) none ht wt_ne_wal j walB
  simp only [and_self, ite_true] at hW
  have hS := entry_rename m j wtB walB (.dir J) none ht wt_ne_wal J segB
  rw [if_neg (fun h => seg_ne_wal h.2.symm), if_neg (fun h => seg_ne_wt h.2.symm)] at hS
  refine ⟨fun i => by rw [hW]; simp, fun J' hJ' => ⟨k, rfl, ?_⟩⟩
  rw [hW] at hJ'
  cases hJ'
  rw [hS, hs]

theorem wt_renamed {j J : Ino} {m : Tree} (ht : m.entry j wtB = some (.dir J)) :
    ((MetaOp.rename j wtB j walB (.dir J) none).apply m).entry j wtB = none := by
  have h := entry_rename m j wtB walB (.dir J) none ht wt_ne_wal j wtB
  rw [if_neg (fun h => wt_ne_wal h.2.symm), if_pos ⟨rfl, rfl⟩] at h
  exact h

/-- `rename(2)` of `dir/wal.tmp` (the directory `J`, in which `seg` is the file of the key `k`) onto
`dir/wal`, absent, the invariant opened around it. -/
theorem wp_dsRename (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (γ : GName) (V : Hist) (k : Ino) (hw : V.now.entry j walB = none) (J : Ino)
    (ht : V.now.entry j wtB = some (.dir J)) (hs : V.now.entry J segB = some (.file k))
    (kc s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) kc s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗
      (∀ (e : w64) (V' : Hist),
        ⌜RenameDirPost V (.rename j wtB j walB (.dir J) none) e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV kc) (PairV (#(child dir wtB)) (#(child dir walB)))))) {{ Φ }} := by
  have hts : lookupH R V (child dir wtB) = some (.dir J) := by
    rw [lookupH_child_root hR hrj V wtB_ok]; exact ht
  have hwn : lookupH R V (child dir walB) = none := by
    rw [lookupH_child_root hR hrj V walB_ok]; exact hw
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  iapply wp_dsStep R j γ V (some k) kc s "Rename" _
    (RenameDirPost V (.rename j wtB j walB (.dir J) none))
    (fun Φ' => wp_osRenameDirG dir wtB walB j J wtB_ok walB_ok wt_ne_wal R V _ _ kc s q_meta
      (lookupH_root hR hrj V) hts hwn dsN_disj Φ')
    (fun e V' h hp => by
      rcases hp with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
      · exact inv_push h hw _ (safeT_rename ht hs)
      · exact h
      · exact inv_push h hw _ (safeT_rename ht hs)) $$ Hos Hinv Ht Hk Hγ HΦ

/-- `rename(2)` of `dir/wal.tmp`, absent, onto `dir/wal` (the retry of a rename that moved it), the
invariant opened around it: it fails, the history unchanged. -/
theorem wp_dsRenameAbsent (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino)
    (hrj : (dir, j) ∈ R) (γ : GName) (V : Hist) (ko : Option Ino)
    (hn : V.now.entry j wtB = none) (kc s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) R j γ -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) kc s (1 : Qp).half.half -∗ ghostVar (GF := GF) γ (1 : Qp).half ko -∗
      (∀ (e : w64) (V' : Hist), ⌜e ≠ 0 ∧ V' = V⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗
        ghostVar (GF := GF) γ (1 : Qp).half ko -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV kc) (PairV (#(child dir wtB)) (#(child dir walB)))))) {{ Φ }} := by
  have hts : lookupH R V (child dir wtB) = none := by
    rw [lookupH_child_root hR hrj V wtB_ok]; exact hn
  iintro #Hos #Hinv Ht Hk Hγ HΦ
  iapply wp_dsStep R j γ V ko kc s "Rename" _ (fun e V' => e ≠ 0 ∧ V' = V)
    (fun Φ' => by
      iintro Hos' Ht' Hk' HΦ'
      iapply wp_osRenameAbsentG dir wtB dir walB j j wtB_ok walB_ok R V _ _ kc s q_meta
        (lookupH_root hR hrj V) (lookupH_root hR hrj V) hts dsN_disj $$ Hos' Ht' Hk'
      iintro %e %he Ht'
      iapply HΦ' $$ %e %V %(And.intro he rfl) Ht')
    (fun e V' h hp => by rw [hp.2]; exact h) $$ Hos Hinv Ht Hk Hγ HΦ

end steps

/-! ## `os` calls, with the invariant -/

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.Remove(d/b)`, a name below a root, `b` not `wal`, `wal` absent: it stays absent. -/
theorem wp_dsRemove (R : Roots) (j : Ino) (γ : GName) (V : Hist) (ko : Option Ino)
    (hw : V.now.entry j walB = none) (d b : GoString) (hb : NameOk b) (hbw : b ≠ walB)
    (hn : ∃ rj ∈ R, CanonBelow rj.1 (child d b)) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗ ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (Val (@! os.Remove)) (Val #(child d b)))
    {{ (err : GoInterface), RET #err; ghostVar γ (1 : Qp).half ko ∗ ∃ V',
        osTree (DFrac.own (1 : Qp).half) R V' ∗ ⌜V'.now.entry j walB = none⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  iloeb as IH generalizing %V %hw Ht Hγ
  ihave Ht := tree_half (L := hG.goose_localGS) _ R V $$ Ht
  wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
  (try wp_auto)
  wp_apply wp_dsUnlink R j γ V ko hw d b hb hbw hn t _ $$ Hos Hinv Ht Hk Hγ as %e %V1 %hw1 Ht Hγ
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V1 %hw1 Ht Hγ HΦ
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hγ
    iexists V1
    iframe Ht
    ipureintro; exact hw1
  rw [decide_eq_false he0]
  wp_auto
  iloeb as IH2 generalizing %V1 %hw1 Ht Hγ
  ihave Ht := tree_half (L := hG.goose_localGS) _ R V1 $$ Ht
  wp_apply wp_osCallBegin R V1 _ _ CoPset.subseteq_top $$ Hos Ht as %t1 Ht Hk
  (try wp_auto)
  wp_apply wp_dsRmdir R j γ V1 ko hw1 d b hb hbw hn t1 _ $$ Hos Hinv Ht Hk Hγ
    as %e1 %V2 %hw2 Ht Hγ
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ %V2 %hw2 Ht Hγ HΦ
  rw [decide_eq_false he14]
  wp_auto
  by_cases he10 : e1 = W64 0
  · rw [decide_eq_true he10]
    wp_auto
    iapply HΦ
    iframe Hγ
    iexists V2
    iframe Ht
    ipureintro; exact hw2
  rw [decide_eq_false he10]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe Hγ
    iexists V2
    iframe Ht
    ipureintro; exact hw2
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe Hγ
    iexists V2
    iframe Ht
    ipureintro; exact hw2

/-- `os.Mkdir(dir/wal.tmp, perm)`, `wal` absent: on success a new, empty directory `J` there; `wal`
absent either way. -/
theorem wp_dsMkdir' (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (γ : GName) (V : Hist) (ko : Option Ino) (hw : V.now.entry j walB = none) (perm : w32) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗ ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (App (Val (@! os.Mkdir)) (Val #(child dir wtB))) (Val #perm))
    {{ (err : GoInterface), RET #err; ghostVar γ (1 : Qp).half ko ∗ ∃ V',
        osTree (DFrac.own (1 : Qp).half) R V' ∗ ⌜V'.now.entry j walB = none ∧
          (err = interface.nil → ∃ J, V'.now.entry j wtB = some (.dir J) ∧
            V'.now.entry J segB = none)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  iloeb as IH generalizing %V %hw Ht Hγ
  ihave Ht := tree_half (L := hG.goose_localGS) _ R V $$ Ht
  wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
  (try wp_auto)
  wp_apply wp_dsMkdir R hR dir j hrj γ V ko hw t _ $$ Hos Hinv Ht Hk Hγ as %e %V' %hp Ht Hγ
  have hkeep : KeepW j V V' := by
    rcases hp with ⟨-, J, -, -, ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨-, rfl⟩
    · exact .inr ⟨_, rfl, walKeep_mkdir j j wtB J wt_ne_wal⟩
    · exact .inl rfl
    · exact .inr ⟨_, rfl, walKeep_mkdir j j wtB J wt_ne_wal⟩
    · exact .inl rfl
  have hw' := keep_wal hw hkeep
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V' %hw' Ht Hγ HΦ
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hγ
    iexists V'
    iframe Ht
    ipureintro
    refine ⟨hw', fun _ => ?_⟩
    rcases hp with ⟨-, J, hJ, hJR, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩
    · have hJj : J ≠ j := fun h => hJR dir (h ▸ hrj)
      refine ⟨J, ?_, ?_⟩
      · rw [Hist.push_now, entry_mkdir, if_neg hJj, if_pos ⟨rfl, rfl⟩]
      · rw [Hist.push_now, entry_mkdir, if_pos rfl]
    · exact absurd he0 h
    · exact absurd he0 h
  rw [decide_eq_false he0]
  wp_auto
  unfold os.model.pathError
  wp_apply wp_errno
  iapply HΦ
  iframe Hγ
  iexists V'
  iframe Ht
  ipureintro
  exact ⟨hw', fun h => by cases h⟩

/-- What a retried `open(2)` with `O_CREAT` of `d/seg` sees: nothing there, or the file it made
(whose `OsMeta` the caller holds). -/
def crStateD (R : Roots) (V : Hist) (J : Ino) : Option Ino → IProp GF
  | none => osTree (GF := GF) (DFrac.own (1 : Qp).half) R V
  | some i => iprop(osTree (GF := GF) (DFrac.own (1 : Qp).half) R
      (V.push ⟨.create J segB i, V.2.length⟩) ∗ osMeta (GF := GF) i (DFrac.own 1) newMeta)

theorem entry_push_create' (V : Hist) (J : Ino) (b : GoString) (i : Ino) (s : Nat) :
    (V.push ⟨.create J b i, s⟩).now.entry J b = some (.file i) := by
  rw [Hist.push_now, entry_create, if_pos ⟨rfl, rfl⟩]

/-- `os.OpenFile(d/seg, O_RDWR|O_CREATE, perm)`, `d` the directory `J`, `seg` absent, `wal` absent:
on success a new file of a fresh inode `i`, `d/seg` names it; `wal` absent either way. -/
theorem wp_dsOpenCreate (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino)
    (hrj : (dir, j) ∈ R) (γ : GName) (V : Hist) (ko : Option Ino) (hw : V.now.entry j walB = none)
    (J : Ino) (ht : V.now.entry j wtB = some (.dir J)) (hn : V.now.entry J segB = none)
    (perm : w32) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗ ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child (child dir wtB) segB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); ghostVar γ (1 : Qp).half ko ∗
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗
            os.ownFile f fd (child (child dir wtB) segB) (DFrac.own 1) ∗
            osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗ osMeta i (DFrac.own 1) newMeta ∗
            osTree (DFrac.own (1 : Qp).half) R (V.push ⟨.create J segB i, V.2.length⟩)) ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ V', osTree (DFrac.own (1 : Qp).half) R V' ∗
            ⌜V'.now.entry j walB = none⌝)) }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  have hd : lookupH R V (child dir wtB) = some (.dir J) := by
    rw [lookupH_child_root hR hrj V wtB_ok]; exact ht
  have hn' : lookupH R V (child (child dir wtB) segB) = none := by rw [lookupH_child_dir hR hd segB_ok]; exact hn
  have hwp : ∀ i, (V.push ⟨.create J segB i, V.2.length⟩).now.entry j walB = none :=
    fun i => keep_wal hw (.inr ⟨_, rfl, walKeep_create j J segB i seg_ne_wal⟩)
  obtain ⟨ko', hko⟩ : ∃ ko' : Option Ino, ko' = none := ⟨_, rfl⟩
  ihave Hs : crStateD R V J ko' $$ [Ht]
  · subst hko; unfold crStateD; iexact Ht
  clear hko
  iloeb as IH generalizing %ko' Hs Hγ
  rw [os.file_ty_eq, os.File_ty_eq]
  cases ko' with
  | none =>
    unfold crStateD
    ihave Ht := tree_half (L := hG.goose_localGS) _ R V $$ Hs
    wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
    rw [show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_dsCreate R j γ V ko hw (child dir wtB) J hd hn' t _ $$ Hos Hinv Ht Hk Hγ as %fd %e Hγ Hr
    icases Hr with (⟨%he, %i, Ht, Hm, Hfd⟩ | ⟨%he, Hst⟩)
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
      iframe Hγ
      ileft
      iexists fd, i
      iframe Hfd Hm Ht
      isplitr
      · ipureintro; exact ⟨rfl, hfd0⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show ¬ e = W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        icases Hst with (Ht | ⟨%i, Ht, Hm⟩)
        · iapply IH $$ %none Ht Hγ HΦ
        · iapply IH $$ %(some i) [Ht Hm] Hγ HΦ
          simp only [crStateD]; iframe
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe Hγ
        iright
        isplitr
        · ipureintro; intro h; cases h
        icases Hst with (Ht | ⟨%i, Ht, -⟩)
        · iexists _; iframe Ht; ipureintro; exact hw
        · iexists _; iframe Ht; ipureintro; exact hwp i
  | some i =>
    unfold crStateD
    icases Hs with ⟨Ht, Hm⟩
    ihave Ht := tree_half (L := hG.goose_localGS) _ R _ $$ Ht
    wp_apply wp_osCallBegin R _ _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
    rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
    (try wp_auto)
    have hl : lookupH R (V.push ⟨.create J segB i, V.2.length⟩) (child (child dir wtB) segB) = some (.file i) := by
      have hd' : lookupH R (V.push ⟨.create J segB i, V.2.length⟩) (child dir wtB) =
          some (.dir J) := by
        rw [lookupH_child_root hR hrj _ wtB_ok, Hist.push_now, entry_create,
          if_neg (fun h => seg_ne_wt h.2)]
        exact ht
      rw [lookupH_child_dir hR hd' segB_ok]; exact entry_push_create' _ _ _ _ _
    wp_apply wp_osOpenFile (child (child dir wtB) segB) (W64 0x80042) R _ _ _ t _ i
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hl
      CoPset.subseteq_top $$ Hos Ht Hk as %fd %e %hres Ht Hfd
    ihave Ht := tree_unhalf (L := hG.goose_localGS) _ R _ $$ Ht
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
      have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
      iapply HΦ
      iframe Hγ
      ileft
      iexists fd, i
      iframe Hfd Hm Ht
      isplitr
      · ipureintro; exact ⟨rfl, hfd0⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · rw [decide_eq_false he0, if_neg (show ¬ e = (0 : w64) from he0)]
      iclear Hfd
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %(some i) [Ht Hm] Hγ HΦ
        simp only [crStateD]; iframe
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe Hγ
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists _; iframe Ht; ipureintro; exact hwp i

/-- `os.Rename(dir/wal.tmp, dir/wal)`, `wal.tmp` the directory `J`, in which `seg` is the file of the
key `k`, `wal` absent: on success renamed. -/
theorem wp_dsRenameWal (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (γ : GName) (V : Hist) (k : Ino) (hw : V.now.entry j walB = none) (J : Ino)
    (ht : V.now.entry j wtB = some (.dir J)) (hs : V.now.entry J segB = some (.file k)) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) }}
      (App (App (Val (@! os.Rename)) (Val #(child dir wtB))) (Val #(child dir walB)))
    {{ (err : GoInterface), RET #err; ghostVar γ (1 : Qp).half (some k) ∗
        ∃ V', osTree (DFrac.own (1 : Qp).half) R V' }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  have hnd : ∀ J', lookupH R V (child dir walB) ≠ some (.dir J') := by
    intro J'; rw [lookupH_child_root hR hrj V walB_ok, hw]; simp
  have htp : (Hist.st R V).TreePath (child dir walB) :=
    .inr (treeName_child (st := Hist.st R V) (lookupH_root hR hrj V) walB_ok)
  ihave Ht := tree_half (L := hG.goose_localGS) _ R V $$ Ht
  wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Ht as %t Ht Hk
  (try wp_auto)
  wp_apply wp_osLstatDir (child dir walB) R V _ _ t _ htp hnd CoPset.subseteq_top $$ Hos Ht Hk
    as %e0 Ht
  ihave Ht := tree_unhalf (L := hG.goose_localGS) _ R V $$ Ht
  (try wp_auto)
  let Vr := V.push ⟨.rename j wtB j walB (.dir J) none, V.2.length⟩
  have hVrt : Vr.now.entry j wtB = none := by
    show (V.push _).now.entry j wtB = none
    rw [Hist.push_now]; exact wt_renamed ht
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = V := ⟨_, rfl⟩
  ihave Ht : osTree (DFrac.own (1 : Qp).half) R V1 $$ [Ht]
  · subst hV1; iexact Ht
  ihave Hp : ⌜V1 = V ∨ V1 = Vr⌝ $$ []
  · ipureintro; exact .inl hV1
  clear hV1
  iloeb as IH generalizing %V1 Hp Ht Hγ
  icases Hp with %Hp
  ihave Ht := tree_half (L := hG.goose_localGS) _ R V1 $$ Ht
  wp_apply wp_osCallBegin R V1 _ _ CoPset.subseteq_top $$ Hos Ht as %t1 Ht Hk
  (try wp_auto)
  rcases Hp with rfl | rfl
  · wp_apply wp_dsRename R hR dir j hrj γ V1 k hw J ht hs t1 _ $$ Hos Hinv Ht Hk Hγ
      as %e %V' %hp Ht Hγ
    have hV' : V' = V1 ∨ V' = Vr := by
      rcases hp with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
      · exact .inr rfl
      · exact .inl rfl
      · exact .inr rfl
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
  · wp_apply wp_dsRenameAbsent R hR dir j hrj γ Vr (some k) hVrt t1 _ $$ Hos Hinv Ht Hk Hγ
      as %e %V' %hp Ht Hγ
    obtain ⟨he, rfl⟩ := hp
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ %Vr [] Ht Hγ HΦ
      ipureintro; exact .inr rfl
    rw [decide_eq_false he4]
    wp_auto
    rw [decide_eq_false (show ¬ e = W64 0 from he)]
    wp_auto
    wp_apply wp_errno
    unfold os.model.linkError
    rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
    wp_auto
    iapply HΦ
    iframe Hγ
    iexists _
    iframe Ht

end oscalls

/-! ## The program -/

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem canon_T (dir : GoString) : CanonBelow dir (child dir wtB) :=
  ⟨[wtB], by simp, by intro c hc; simp at hc; subst hc; exact wtB_ok, by simp [joinPath, child]⟩

theorem canon_Ts (dir : GoString) : CanonBelow dir (child (child dir wtB) segB) :=
  ⟨[wtB, segB], by simp, by
    intro c hc; simp at hc; rcases hc with rfl | rfl
    · exact wtB_ok
    · exact segB_ok, by simp [joinPath, child]⟩

/-- `Create(dir)`, `dir` the root of `j`, `wal` absent: it does not panic. -/
theorem wp_Create (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (γ : GName)
    (V : Hist) (ko : Option Ino) (hw : V.now.entry j walB = none) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗ ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Create)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ⟩
  (try wp_auto)
  try rw [show dir ++ go!"/wal.tmp" = child dir wtB from rfl]
  try rw [show child dir wtB ++ go!"/seg" = child (child dir wtB) segB from rfl]
  -- `Remove(tmp/seg)`
  wp_apply wp_dsRemove R j γ V ko hw (child dir wtB) segB segB_ok seg_ne_wal
      ⟨(dir, j), hrj, canon_Ts dir⟩ $$ [Hos Hinv Ht Hγ] as %err1 ⟨Hγ, %V1, Ht, %hw1⟩
  · iframe; iframe #
  (try wp_auto)
  -- `Remove(tmp)`
  wp_apply wp_dsRemove R j γ V1 ko hw1 dir wtB wtB_ok wt_ne_wal ⟨(dir, j), hrj, canon_T dir⟩
      $$ [Hos Hinv Ht Hγ] as %err2 ⟨Hγ, %V2, Ht, %hw2⟩
  · iframe; iframe #
  (try wp_auto)
  -- `Mkdir(tmp)`
  wp_apply wp_dsMkdir' R hR dir j hrj γ V2 ko hw2 (W32 488)
      $$ [Hos Hinv Ht Hγ] as %err3 ⟨Hγ, %V3, Ht, %hV3⟩
  · iframe; iframe #
  obtain ⟨hw3, hok3⟩ := hV3
  cases err3 with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  obtain ⟨J, hT3, hTs3⟩ := hok3 rfl
  have hd3 : lookupH R V3 (child dir wtB) = some (.dir J) := by
    rw [lookupH_child_root hR hrj V3 wtB_ok]; exact hT3
  (try wp_auto)
  -- `OpenFile(tmp/seg, O_RDWR|O_CREATE)`
  rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
  rw [show child dir wtB ++ go!"/seg" = child (child dir wtB) segB from rfl]
  wp_apply wp_dsOpenCreate R hR dir j hrj γ V3 ko hw3 J hT3 hTs3 (W32 438)
      $$ [Hos Hinv Ht Hγ] as %f %err ⟨Hγ, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%fd, %i, %hek, Hf, Hfd, Hm, Ht⟩ | ⟨%herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -⟩ := hek
  (try wp_auto)
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  ihave Hb0 : osBytes (GF := GF) i (W64 0).toNat (DFrac.own 1) [] $$ []
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  ihave Hmc : mcellsAny (GF := GF) newMeta.maps (W64 0).toNat ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny; rw [show newMeta.maps = ∅ from rfl]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_WriteAt f fd (child (child dir wtB) segB) (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0)
      (DFrac.own 1) ⟨i, true, true⟩ 1 newMeta [] rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (fun _ => rfl) (.inl rfl) $$ [Hos Hf Hsl Hfd Hm Hb0 Hmc]
    as %n %err ⟨Hf, Hsl, Hfd, %j', %ys, %h, %v, %r, %Hres, Hm, Hys, -⟩
  · iframe; iexact Hos
  obtain ⟨hj, -, hys, -, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  have hys' : ys.map Prod.fst = dataC := by rw [hys]; exact pwBytes_data
  (try wp_auto)
  -- `f.Sync()`
  wp_apply wp_Sync f fd (child (child dir wtB) segB) (DFrac.own 1) (DFrac.own 1) ⟨i, true, true⟩ _
      0 ys $$ [Hos Hf Hfd Hm Hys] as %err ⟨Hf, Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm, Hys⟩ | ⟨%he, -, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  subst he
  (try wp_auto)
  wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; iexact Hos
  (try wp_auto)
  -- the file, durable, goes into the invariant under the key `i`
  generalize hV4 : V3.push ⟨.create J segB i, V3.2.length⟩ = V4
  have hw4 : V4.now.entry j walB = none := by
    rw [← hV4]; exact keep_wal hw3 (.inr ⟨_, rfl, walKeep_create j J segB i seg_ne_wal⟩)
  have hT4 : V4.now.entry j wtB = some (.dir J) := by
    rw [← hV4, Hist.push_now, entry_create, if_neg (fun h => seg_ne_wt h.2), hT3]
  have hTs4 : V4.now.entry J segB = some (.file i) := by rw [← hV4]; exact entry_push_create' _ _ _ _ _
  icases (osMeta_halves i _).1 $$ Hm with ⟨-, Hmi⟩
  icases (osBytes_halves i 0 _).1 $$ Hys with ⟨-, Hysi⟩
  ihave Hk : keyRes (L := hG.goose_localGS) (some i) $$ [Hmi Hysi]
  · unfold keyRes
    iexists _, _
    iframe Hmi Hysi
    ipureintro; exact synced_good _ rfl rfl ys hys'
  imod ds_deposit R j γ V4 ko i hw4 $$ Hinv Ht Hγ Hk with ⟨Ht, Hγ⟩
  -- `Rename(tmp, dir/wal)`
  try rw [show dir ++ go!"/wal" = child dir walB from rfl]
  wp_apply wp_dsRenameWal R hR dir j hrj γ V4 i hw4 J hT4 hTs4 $$ [Hos Hinv Ht Hγ]
    as %err ⟨Hγ, %V5, Ht⟩
  · iframe; iframe #
  cases err with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  (try wp_auto)
  -- the directory's sync
  wp_apply wp_syncDir R hR dir j hrj V5 _ $$ [Hos Ht] as %ok Ht
  · iframe; iexact Hos
  (try wp_auto)
  iapply HΦ
  itrivial

/-- `checkDir(w)`, `w` the directory `J`, its `seg` the file `k`, of which the program has half,
`CheckOk`: it does not panic. -/
theorem wp_checkDir (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (R : Roots) (hR : RootsOk R) (w : GoString) (J k : Ino) (q : Qp) (V : Hist)
    (hw : lookupH R V w = some (.dir J)) (hk : V.now.entry J segB = some (.file k))
    (m : OsMeta) (bs : List (w8 × Bool)) (hok : CheckOk m bs) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V ∗
        osMeta (GF := GF) k (DFrac.own (1 : Qp).half) m ∗
        osBytes (GF := GF) k 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.checkDir)) (Val #w))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, Ht, Hm, Hb⟩
  (try wp_auto)
  wp_apply wp_readNamesT w q R V J hw $$ [Hos Ht] as %sl %ok ⟨Ht, Hr⟩
  · iframe; iexact Hos
  icases Hr with (%hok' | ⟨%names, %hn, Hsl⟩)
  · subst hok'
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hnodup, hmem⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧ segB ∉ names.take (sint.nat i)⌝)
      $$ [i n]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_⟩ <;> rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hns⟩ := Hi
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
    by_cases hbs : b = segB
    · subst hbs
      rw [decide_eq_true (show segB = go!"seg" from rfl)]
      (try wp_auto)
      wp_apply wp_check wp_ReadAt wp_Close R w V q k
          (by rw [lookupH_child_dir hR hw segB_ok]; exact hk) m bs hok
        $$ [Hos Ht Hm Hb]
      · iframe; iexact Hos
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    rw [decide_eq_false (show ¬ b = go!"seg" from hbs)]
    (try wp_auto)
    wp_for_post
    iframe
    iexists i + W64 1, b
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [htake]; simp [hns, Ne.symm hbs]
  · -- the loop is done: `seg` was not among the names, which it is
    exfalso
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hns
    apply hns
    rw [hmem, hk]; rfl

/-- `BootDir(dir)`, `dir` the root of `j`, from the history `V` whose tree is `SafeT` with the
invariant's key `ko`, of whose file the program has half (`segRes`): it does not panic. -/
theorem wp_BootDir (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (γ : GName)
    (V : Hist) (ko : Option Ino) (hs : SafeT j ko V.now) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) R j γ ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗ ghostVar (GF := GF) γ (1 : Qp).half ko ∗
        segRes (GF := GF) ko }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.BootDir)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Ht, Hγ, Hs⟩
  (try wp_auto)
  wp_apply wp_readNamesT dir _ R V j (lookupH_root hR hrj V) $$ [Hos Ht] as %sl %ok ⟨Ht, Hr⟩
  · iframe; iexact Hos
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hnodup, hmem⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧ walB ∉ names.take (sint.nat i)⌝)
      $$ [i n]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_⟩ <;> rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hns⟩ := Hi
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
    by_cases hbs : b = walB
    · subst hbs
      rw [decide_eq_true (show walB = go!"wal" from rfl)]
      (try wp_auto)
      -- `wal` is there: a directory, its `seg` the file of the key
      have hW : (V.now.entry j walB).isSome := (hmem walB).1 (List.mem_of_getElem? hb)
      obtain ⟨J, hWd⟩ : ∃ J, V.now.entry j walB = some (.dir J) := by
        cases h : V.now.entry j walB with
        | none => rw [h] at hW; cases hW
        | some x =>
          cases x with
          | dir J => exact ⟨J, rfl⟩
          | file k => exact absurd h (hs.1 k)
      obtain ⟨k, rfl, hk⟩ := hs.2 J hWd
      unfold segRes
      icases Hs with ⟨%m, %bs, Hm, Hb, %hok⟩
      try rw [show dir ++ go!"/wal" = child dir walB from rfl]
      wp_apply wp_checkDir wp_ReadAt wp_Close R hR (child dir walB) J k _ V
          (by rw [lookupH_child_root hR hrj V walB_ok]; exact hWd) hk m bs hok
        $$ [Hos Ht Hm Hb]
      · iframe; iexact Hos
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    rw [decide_eq_false (show ¬ b = go!"wal" from hbs)]
    (try wp_auto)
    wp_for_post
    iframe
    iexists i + W64 1, b
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [htake]; simp [hns, Ne.symm hbs]
  · -- the loop is done: no `wal`
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hns
    have hWn : V.now.entry j walB = none := by
      cases h : V.now.entry j walB with
      | none => rfl
      | some x => exact absurd ((hmem walB).2 (by rw [h]; rfl)) hns
    (try wp_auto)
    wp_apply wp_Create wp_Close wp_WriteAt wp_Sync R hR dir j hrj γ V ko hWn
      $$ [Hos Hinv Ht Hγ]
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial

end prog

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
