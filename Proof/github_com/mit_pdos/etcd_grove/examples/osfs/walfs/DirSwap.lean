/-
The proofs of `examples/osfs/walfs`'s `dirswap.go` (one generation): the crash invariant of the
namespace under `dir`, and the specs of `Create`, `checkDir` and `BootDir`.

The invariant (`dsInv`) holds half of the namespace's history (`osNsAll`) and says of every
prefix of it, so of every crash outcome (`SafeH`): `dir` is a directory, neither `wal.tmp` nor
`wal` is a file, and if `wal` is a directory, its `seg` is the file of the key `ko`, a ghost
variable whose other half the program keeps, with half of that file's `OsMeta` and bytes, every
crash of which leaves the data (`keyRes`, `Boot.lean`). The program keeps the other half of the
history, and opens the invariant around each call that changes the namespace (`unlink`, `rmdir`,
`mkdir`, `open(O_CREAT)`, `rename`). `Create` makes `wal` appear only by renaming `wal.tmp` onto
it, in which `seg` is then the new file, written and made durable: before the rename it deposits
that file under the key, which it may change as `wal` was absent all along (`WAbs`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot
public import GooseLang.Ext.OsFs.NsSpecsDirMk
public import GooseLang.Ext.OsFs.NsSpecsDirMv
public import Spec.os.File__Sync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

/-! ## The names -/

def walB : GoString := go!"wal"
def wtB : GoString := go!"wal.tmp"

theorem walB_ok : NameOk walB := by decide
theorem wtB_ok : NameOk wtB := by decide
theorem wt_ne_wal : wtB ≠ walB := by decide

theorem child_ne_self (d b : GoString) : child d b ≠ d := by
  intro h; have := congrArg List.length h; simp at this

theorem child_child_ne (d b c : GoString) : child (child d b) c ≠ d := by
  intro h; have := congrArg List.length h; simp at this; try omega

theorem child_inj {d b b' : GoString} (h : child d b = child d b') : b = b' := by
  have := List.append_cancel_left h; simpa using this

theorem child_child_ne_child {d b c b' : GoString} (h : b ++ slashB :: c ≠ b') :
    child (child d b) c ≠ child d b' := by
  intro he; apply h; apply child_inj (d := d); simpa [child] using he

theorem child_child_inj {d b c b' c' : GoString} (h : child (child d b) c = child (child d b') c') :
    b ++ slashB :: c = b' ++ slashB :: c' := by
  apply child_inj (d := d); simpa [child] using h

/-- `T`, `W`, `W/seg`, `T/seg`: pairwise apart, and none `dir`. -/
theorem T_ne_W (dir : GoString) : child dir wtB ≠ child dir walB :=
  fun h => wt_ne_wal (child_inj h)

theorem Ts_ne_W (dir : GoString) : child (child dir wtB) segB ≠ child dir walB :=
  child_child_ne_child (by decide)

theorem Ts_ne_T (dir : GoString) : child (child dir wtB) segB ≠ child dir wtB := child_ne_self _ _

theorem Ws_ne_T (dir : GoString) : child (child dir walB) segB ≠ child dir wtB :=
  child_child_ne_child (by decide)

theorem Ts_ne_Ws (dir : GoString) : child (child dir wtB) segB ≠ child (child dir walB) segB :=
  fun h => absurd (child_child_inj h) (by decide)

theorem T_ne_Ws (dir : GoString) : child dir wtB ≠ child (child dir walB) segB :=
  fun h => Ws_ne_T dir h.symm

/-! ## What every crash outcome must be -/

/-- **The state a boot may find**: `dir` a directory; `wal.tmp` and `wal` no files; if `wal` is a
directory, its `seg` the file of the key `ko`. -/
def Safe (dir : GoString) (ko : Option GoString) (m : NsMap) : Prop :=
  m !! dir = some .dir ∧ (∀ k, m !! child dir wtB ≠ some (.file k)) ∧
  (∀ k, m !! child dir walB ≠ some (.file k)) ∧
  (m !! child dir walB = some .dir →
    ∃ k, ko = some k ∧ m !! child (child dir walB) segB = some (.file k))

/-- Every prefix of the history `V` is `Safe`. -/
def SafeH (dir : GoString) (ko : Option GoString) (V : NsMap × List NsOp) : Prop :=
  ∀ n, Safe dir ko (nsReplay (V.2.take n) V.1)

/-- `wal` is absent from every prefix of the history `V`. -/
def WAbs (dir : GoString) (V : NsMap × List NsOp) : Prop :=
  ∀ n, nsReplay (V.2.take n) V.1 !! child dir walB = none

theorem replay_push_take (V : NsMap × List NsOp) (o : NsOp) (n : Nat) :
    nsReplay ((nsPush V o).2.take n) (nsPush V o).1 = nsReplay (V.2.take n) V.1 ∨
      (nsReplay ((nsPush V o).2.take n) (nsPush V o).1 = o.apply (nsReplay V.2 V.1)) := by
  by_cases hn : n ≤ V.2.length
  · left; show nsReplay ((V.2 ++ [o]).take n) V.1 = _
    rw [List.take_append_of_le_length hn]
  · right; show nsReplay ((V.2 ++ [o]).take n) V.1 = _
    rw [List.take_of_length_le (by simp; omega), nsReplay_snoc]

theorem replay_push (V : NsMap × List NsOp) (o : NsOp) :
    nsReplay (nsPush V o).2 (nsPush V o).1 = o.apply (nsReplay V.2 V.1) := nsReplay_snoc _ _ _

theorem safeH_now {dir : GoString} {ko : Option GoString} {V : NsMap × List NsOp}
    (h : SafeH dir ko V) : Safe dir ko (nsReplay V.2 V.1) := by
  have := h V.2.length; rwa [List.take_length] at this

theorem safeH_push {dir : GoString} {ko : Option GoString} {V : NsMap × List NsOp} {o : NsOp}
    (h : SafeH dir ko V) (ho : Safe dir ko (o.apply (nsReplay V.2 V.1))) :
    SafeH dir ko (nsPush V o) := by
  intro n
  rcases replay_push_take V o n with he | he <;> rw [he]
  · exact h n
  · exact ho

theorem wabs_now {dir : GoString} {V : NsMap × List NsOp} (h : WAbs dir V) :
    nsReplay V.2 V.1 !! child dir walB = none := by
  have := h V.2.length; rwa [List.take_length] at this

theorem wabs_push {dir : GoString} {V : NsMap × List NsOp} {o : NsOp} (h : WAbs dir V)
    (ho : o.apply (nsReplay V.2 V.1) !! child dir walB = none) : WAbs dir (nsPush V o) := by
  intro n
  rcases replay_push_take V o n with he | he <;> rw [he]
  · exact h n
  · exact ho

theorem wabs_nil (dir : GoString) (m : NsMap) (h : m !! child dir walB = none) :
    WAbs dir (m, []) := fun n => by simp only [List.take_nil]; exact h

/-- With `wal` absent all along, the key does not matter. -/
theorem safeH_rekey {dir : GoString} {ko ko' : Option GoString} {V : NsMap × List NsOp}
    (h : SafeH dir ko V) (hw : WAbs dir V) : SafeH dir ko' V := by
  intro n
  obtain ⟨h1, h2, h3, -⟩ := h n
  exact ⟨h1, h2, h3, fun hd => by rw [hw n] at hd; cases hd⟩

/-- A path other than `dir`, `wal` and `wal/seg` removed: still `Safe`. -/
theorem safe_delete {dir p : GoString} {ko : Option GoString} {m : NsMap} (h : Safe dir ko m)
    (h1 : p ≠ dir) (h2 : p ≠ child dir walB) (h3 : p ≠ child (child dir walB) segB) :
    Safe dir ko (GMap.delete p m) := by
  obtain ⟨hd, ht, hw, hs⟩ := h
  refine ⟨by rw [GMap.lookup_delete_ne _ h1]; exact hd, fun k => ?_, fun k => ?_, fun hwd => ?_⟩
  · by_cases hp : p = child dir wtB
    · subst hp; rw [GMap.lookup_delete_eq]; simp
    · rw [GMap.lookup_delete_ne _ hp]; exact ht k
  · rw [GMap.lookup_delete_ne _ h2]; exact hw k
  · rw [GMap.lookup_delete_ne _ h2] at hwd
    rw [GMap.lookup_delete_ne _ h3]; exact hs hwd

/-- A directory made at a path other than `dir`, `wal` and `wal/seg`: still `Safe`. -/
theorem safe_insert_dir {dir p : GoString} {ko : Option GoString} {m : NsMap} (h : Safe dir ko m)
    (h1 : p ≠ dir) (h2 : p ≠ child dir walB) (h3 : p ≠ child (child dir walB) segB) :
    Safe dir ko (<[p := .dir]> m) := by
  obtain ⟨hd, ht, hw, hs⟩ := h
  refine ⟨by rw [GMap.lookup_insert_ne _ _ h1]; exact hd, fun k => ?_, fun k => ?_, fun hwd => ?_⟩
  · by_cases hp : p = child dir wtB
    · subst hp; rw [GMap.lookup_insert_eq]; simp
    · rw [GMap.lookup_insert_ne _ _ hp]; exact ht k
  · rw [GMap.lookup_insert_ne _ _ h2]; exact hw k
  · rw [GMap.lookup_insert_ne _ _ h2] at hwd
    rw [GMap.lookup_insert_ne _ _ h3]; exact hs hwd

/-- A file made at a path other than `dir`, `wal.tmp`, `wal` and `wal/seg`: still `Safe`. -/
theorem safe_insert_file {dir p k : GoString} {ko : Option GoString} {m : NsMap} (h : Safe dir ko m)
    (h1 : p ≠ dir) (h0 : p ≠ child dir wtB) (h2 : p ≠ child dir walB)
    (h3 : p ≠ child (child dir walB) segB) :
    Safe dir ko (<[p := .file k]> m) := by
  obtain ⟨hd, ht, hw, hs⟩ := h
  refine ⟨by rw [GMap.lookup_insert_ne _ _ h1]; exact hd, fun k => ?_, fun k => ?_, fun hwd => ?_⟩
  · rw [GMap.lookup_insert_ne _ _ h0]; exact ht k
  · rw [GMap.lookup_insert_ne _ _ h2]; exact hw k
  · rw [GMap.lookup_insert_ne _ _ h2] at hwd
    rw [GMap.lookup_insert_ne _ _ h3]; exact hs hwd

theorem isUnder_child_child (d b c : GoString) : IsUnder (child d b) (child (child d b) c) :=
  (isUnder_iff _ _).2 ⟨slashB :: c, by simp [child], .inr ⟨c, rfl⟩⟩

theorem not_isUnder_child_self (d b : GoString) : ¬ IsUnder (child d b) d := by
  intro h
  obtain ⟨r, hr, -⟩ := (isUnder_iff _ _).1 h
  have := congrArg List.length hr; simp at this; try omega

theorem not_isUnder_W_T (dir : GoString) : ¬ IsUnder (child dir walB) (child dir wtB) := by
  intro h
  obtain ⟨r, hr, hr'⟩ := (isUnder_iff _ _).1 h
  have h' : wtB = walB ++ r := by
    have := List.append_cancel_left (show dir ++ (slashB :: wtB) = dir ++ (slashB :: walB ++ r) by
      rw [← List.append_assoc]; exact hr)
    simpa using this
  rcases hr' with rfl | ⟨r', rfl⟩
  · exact wt_ne_wal (by simpa using h')
  · have := congrArg (·[3]?) h'
    simp [wtB, walB] at this
    revert this; decide

theorem not_isUnder_T_W (dir : GoString) : ¬ IsUnder (child dir wtB) (child dir walB) := by
  intro h
  obtain ⟨r, hr, -⟩ := (isUnder_iff _ _).1 h
  have := congrArg List.length hr; simp [wtB, walB] at this; try omega

/-- **`wal.tmp` renamed onto `wal`**, absent, `wal.tmp/seg` the file of `k`: `Safe` with the key
`k`. -/
theorem safe_rename {dir k : GoString} {ko : Option GoString} {m m' : NsMap} (h : Safe dir ko m)
    (htd : m !! child dir wtB = some .dir) (hts : m !! child (child dir wtB) segB = some (.file k))
    (h1 : ∀ r, (r = [] ∨ ∃ r', r = slashB :: r') →
      m' !! (child dir walB ++ r) = m !! (child dir wtB ++ r))
    (h2 : ∀ y, IsUnder (child dir wtB) y → ¬ IsUnder (child dir walB) y → m' !! y = none)
    (h3 : ∀ y, ¬ IsUnder (child dir wtB) y → ¬ IsUnder (child dir walB) y → m' !! y = m !! y) :
    Safe dir (some k) m' := by
  have hW : m' !! child dir walB = some .dir := by
    have := h1 [] (.inl rfl); simp only [List.append_nil] at this; rw [this, htd]
  refine ⟨?_, fun k' => ?_, fun k' => by rw [hW]; simp, fun _ => ⟨k, rfl, ?_⟩⟩
  · rw [h3 _ (not_isUnder_child_self _ _) (not_isUnder_child_self _ _)]; exact h.1
  · rw [h2 _ (.inl rfl) (not_isUnder_W_T dir)]; simp
  · have e1 : child (child dir walB) segB = child dir walB ++ slashB :: segB := by simp [child]
    have e2 : child (child dir wtB) segB = child dir wtB ++ slashB :: segB := by simp [child]
    have := h1 (slashB :: segB) (.inr ⟨segB, rfl⟩)
    rw [e1, this, ← e2, hts]

/-! ## The invariant -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **The crash invariant** of the namespace under `dir`. -/
def dsInv (dir : GoString) (γ : GName) : IProp GF :=
  inv bootN iprop(∃ (V : NsMap × List NsOp) (ko : Option GoString),
    osNsAll (L := L) (DFrac.own (1 : Qp).half) V ∗ ghostVar γ (1 : Qp).half ko ∗
    ⌜SafeH dir ko V⌝ ∗ keyRes (L := L) ko)

instance dsInv_persistent (dir : GoString) (γ : GName) : Persistent (dsInv (L := L) dir γ) := by
  unfold dsInv; infer_instance

instance osNsAll_timeless (dq : DFrac) (V : NsMap × List NsOp) :
    Timeless (osNsAll (L := L) dq V) := by
  unfold osNsAll; infer_instance

theorem osNsAll_halves (V : NsMap × List NsOp) :
    osNsAll (L := L) (DFrac.own 1) V ⊣⊢
      osNsAll (L := L) (DFrac.own (1 : Qp).half) V ∗ osNsAll (L := L) (DFrac.own (1 : Qp).half) V := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () (1 : Qp).half (1 : Qp).half V
  rw [Qp.half_add_half] at h
  exact h

theorem osNsAll_agree (dq1 dq2 : DFrac) (V1 V2 : NsMap × List NsOp) :
    ⊢ osNsAll (L := L) dq1 V1 -∗ osNsAll (L := L) dq2 V2 -∗ ⌜V1 = V2⌝ := by
  unfold osNsAll; iintro A B
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ A B with %hv
  ipureintro; exact hv.2

/-- The invariant opened around a step that keeps the key: the whole history, and what closes it
again with a history that is still `SafeH`. -/
theorem ds_acc (dir : GoString) (γ : GName) (V : NsMap × List NsOp) :
    ⊢ dsInv (L := L) dir γ -∗ osNsAll (L := L) (DFrac.own (1 : Qp).half) V ={⊤, ⊤ \ ↑bootN}=∗
      ∃ ko, osNsAll (L := L) (DFrac.own 1) V ∗ ⌜SafeH dir ko V⌝ ∗
        (∀ V', ⌜SafeH dir ko V'⌝ -∗ osNsAll (L := L) (DFrac.own 1) V' ={⊤ \ ↑bootN, ⊤}=∗
          osNsAll (L := L) (DFrac.own (1 : Qp).half) V') := by
  iintro #Hinv HV
  unfold dsInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko, >HV1, >Hv, >%Hs, >Hk⟩
  icases osNsAll_agree _ _ V V1 $$ HV HV1 with %he
  subst he
  ihave HVw := (osNsAll_halves V).2 $$ [HV HV1]
  · iframe
  imodintro
  iexists ko
  iframe HVw
  isplitr
  · ipureintro; exact Hs
  iintro %V' %Hs' HV'
  icases (osNsAll_halves V').1 $$ HV' with ⟨HV', HV1⟩
  imod Hclose $$ [HV1 Hv Hk] with -
  · inext; iexists V', ko; iframe; ipureintro; exact Hs'
  imodintro
  iexact HV'

/-- The invariant consulted: `dir` is a directory in every prefix of the history. -/
theorem ds_allDir (dir : GoString) (γ : GName) (V : NsMap × List NsOp) :
    ⊢ dsInv (L := L) dir γ -∗ osNsAll (L := L) (DFrac.own (1 : Qp).half) V ={⊤}=∗
      osNsAll (L := L) (DFrac.own (1 : Qp).half) V ∗ ⌜AllDir V dir⌝ := by
  iintro #Hinv HV
  unfold dsInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko, >HV1, >Hv, >%Hs, >Hk⟩
  icases osNsAll_agree _ _ V V1 $$ HV HV1 with %he
  subst he
  imod Hclose $$ [HV1 Hv Hk] with -
  · inext; iexists V, ko; iframe; ipureintro; exact Hs
  imodintro
  iframe HV
  ipureintro; exact fun n => (Hs n).1

/-- With `wal` absent from every prefix of the history, a new key and its file deposited. -/
theorem ds_deposit (dir : GoString) (γ : GName) (V : NsMap × List NsOp) (ko : Option GoString)
    (k : GoString) (hw : WAbs dir V) :
    ⊢ dsInv (L := L) dir γ -∗ osNsAll (L := L) (DFrac.own (1 : Qp).half) V -∗
      ghostVar γ (1 : Qp).half ko -∗ keyRes (L := L) (some k) ={⊤}=∗
      osNsAll (L := L) (DFrac.own (1 : Qp).half) V ∗ ghostVar γ (1 : Qp).half (some k) := by
  iintro #Hinv HV Hγ Hk
  unfold dsInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko1, >HV1, >Hv, >%Hs, >-⟩
  icases osNsAll_agree _ _ V V1 $$ HV HV1 with %he
  subst he
  imod ghostVar_update_halves (some k) γ _ _ $$ Hγ Hv with ⟨Hγ, Hv⟩
  imod Hclose $$ [HV1 Hv Hk] with -
  · inext; iexists V, (some k); iframe; ipureintro; exact safeH_rekey Hs hw
  imodintro
  iframe

end res

/-! ## The calls that change the namespace, with the invariant -/

theorem safeH_or_push {dir : GoString} {ko : Option GoString} {V V' : NsMap × List NsOp} {o : NsOp}
    (h : SafeH dir ko V) (ho : Safe dir ko (o.apply (nsReplay V.2 V.1)))
    (hV : V' = V ∨ V' = nsPush V o) : SafeH dir ko V' := by
  rcases hV with rfl | rfl
  · exact h
  · exact safeH_push h ho

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- `unlink(2)` of `d/b`, a path whose removal keeps every state `Safe`, the invariant opened
around it. -/
theorem wp_dsUnlink (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : ∀ ko m, Safe dir ko m → NsBelowDir m d)
    (hs : ∀ ko m, Safe dir ko m → Safe dir ko (GMap.delete (child d b) m)) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) dir γ -∗
      osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(∃ k, nsReplay V.2 V.1 !! child d b = some (.file k)) ∧
            ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d b)))) {{ Φ }} := by
  iintro #Hos #Hinv HV Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod ds_acc dir γ V $$ Hinv HV with ⟨%ko, HV, %Hs, Hclose⟩
  imodintro
  iapply wp_osUnlinkG d b hb V (hd ko _ (safeH_now Hs)) bootN_disj $$ Hos HV Hz
  iintro %e %V' %hres HV Hz
  have hV : V' = V ∨ V' = nsPush V (.remove (child d b)) := by
    rcases hres with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, h⟩
    · exact .inr h
    · exact h
    · exact .inl h
  imod Hclose $$ %V' %(safeH_or_push (o := .remove (child d b)) Hs (hs ko _ (safeH_now Hs)) hV) HV with HV
  imodintro
  iapply HΦ $$ %e %V' %hres HV Hz

/-- `rmdir(2)` of `d/b`, a path whose removal keeps every state `Safe`, the invariant opened
around it. -/
theorem wp_dsRmdir (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : ∀ ko m, Safe dir ko m → NsBelowDir m d)
    (hs : ∀ ko m, Safe dir ko m → Safe dir ko (GMap.delete (child d b) m)) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) dir γ -∗
      osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(nsReplay V.2 V.1 !! child d b = some .dir ∧
            ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b)))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rmdir" (Val (#(child d b)))) {{ Φ }} := by
  iintro #Hos #Hinv HV Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod ds_acc dir γ V $$ Hinv HV with ⟨%ko, HV, %Hs, Hclose⟩
  imodintro
  iapply wp_osRmdirG d b hb V (hd ko _ (safeH_now Hs)) bootN_disj $$ Hos HV Hz
  iintro %e %V' %hres HV Hz
  have hres' : (nsReplay V.2 V.1 !! child d b = some .dir ∧
      ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
       (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b)))))) ∨ (e ≠ 0 ∧ V' = V) := by
    rcases hres with ⟨h1, -, h⟩ | h
    · exact .inl ⟨h1, h⟩
    · exact .inr h
  have hV : V' = V ∨ V' = nsPush V (.remove (child d b)) := by
    rcases hres' with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, h⟩
    · exact .inr h
    · exact h
    · exact .inl h
  imod Hclose $$ %V' %(safeH_or_push (o := .remove (child d b)) Hs (hs ko _ (safeH_now Hs)) hV) HV with HV
  imodintro
  iapply HΦ $$ %e %V' %hres' HV Hz

/-- `mkdir(2)` of `d/b`, a path where a directory keeps every state `Safe`, the invariant opened
around it. -/
theorem wp_dsMkdir (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : ∀ ko m, Safe dir ko m → NsBelowDir m d)
    (hs : ∀ ko m, Safe dir ko m → Safe dir ko (<[child d b := .dir]> m)) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) dir γ -∗
      osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(nsReplay V.2 V.1 !! child d b = none ∧ nsReplay V.2 V.1 !! d = some .dir ∧
            (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none) ∧
            ((e = 0 ∧ V' = nsPush V (.mkdir (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.mkdir (child d b)))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Mkdir" (Val (#(child d b)))) {{ Φ }} := by
  iintro #Hos #Hinv HV Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod ds_acc dir γ V $$ Hinv HV with ⟨%ko, HV, %Hs, Hclose⟩
  imodintro
  iapply wp_osMkdirG d b hb V (hd ko _ (safeH_now Hs)) bootN_disj $$ Hos HV Hz
  iintro %e %V' %hres HV Hz
  have hV : V' = V ∨ V' = nsPush V (.mkdir (child d b)) := by
    rcases hres with ⟨-, -, -, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, h⟩
    · exact .inr h
    · exact h
    · exact .inl h
  imod Hclose $$ %V' %(safeH_or_push (o := .mkdir (child d b)) Hs (hs ko _ (safeH_now Hs)) hV) HV with HV
  imodintro
  iapply HΦ $$ %e %V' %hres HV Hz

/-- What a retried `open(2)` with `O_CREAT` of `d/b` sees: the history `V`, or the file created
(under the key `k`, whose `OsMeta` the caller holds). -/
def crStateG (p : GoString) (V : NsMap × List NsOp) : Option GoString → IProp GF
  | none => osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V
  | some k => iprop(⌜IsInoKey k⌝ ∗ osNsAll (GF := GF) (DFrac.own (1 : Qp).half) (nsPush V (.create p k)) ∗
      osMeta (GF := GF) k (DFrac.own 1) (some newMeta))

/-- `open(2)` with `O_RDWR | O_CREAT` of `d/b`, absent from the directory `d` of `V`, a path
where a file keeps every state `Safe`, from `V` or after it was created, the invariant opened
around it. -/
theorem wp_dsCreate_any (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (hn : nsReplay V.2 V.1 !! child d b = none)
    (hs : ∀ ko m k, Safe dir ko m → Safe dir ko (<[child d b := .file k]> m))
    (ko : Option GoString) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) dir γ -∗ crStateG (child d b) V ko -∗
      osNsBusy (GF := GF) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (GF := GF) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osNsAll (GF := GF) (DFrac.own (1 : Qp).half) (nsPush V (.create (child d b) k)) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta) ∗
            osFd (GF := GF) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ ∃ ko', crStateG (child d b) V ko')) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) {{ Φ }} := by
  iintro #Hos #Hinv Hs Hz HΦ
  cases ko with
  | none =>
    unfold crStateG
    iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
    imod ds_acc dir γ V $$ Hinv Hs with ⟨%ko, HV, %Hsf, Hclose⟩
    imodintro
    iapply wp_osNsOpenCreateG d b hb V hd hn bootN_disj $$ Hos HV Hz
    iintro %fd %e Hz Hr
    have hpush : ∀ k, SafeH dir ko (nsPush V (.create (child d b) k)) :=
      fun k => safeH_push Hsf (hs ko _ k (safeH_now Hsf))
    icases Hr with (⟨%he, %k, %hk, HV, Hm, Hfd⟩ | ⟨%he, (HV | ⟨%k, %hk, HV, Hm⟩)⟩)
    · imod Hclose $$ %_ %(hpush k) HV with HV
      imodintro
      iapply HΦ $$ %fd %e Hz
      ileft
      isplitr
      · ipureintro; exact he
      iexists k
      iframe
      ipureintro; exact hk
    · imod Hclose $$ %_ %Hsf HV with HV
      imodintro
      iapply HΦ $$ %fd %e Hz
      iright
      isplitr
      · ipureintro; exact he
      iexists none; iexact HV
    · imod Hclose $$ %_ %(hpush k) HV with HV
      imodintro
      iapply HΦ $$ %fd %e Hz
      iright
      isplitr
      · ipureintro; exact he
      iexists (some k)
      dsimp only [crStateG]
      iframe
      ipureintro; exact hk
  | some k =>
    unfold crStateG
    icases Hs with ⟨%hk, HV, Hm⟩
    have hd' : nsReplay (nsPush V (.create (child d b) k)).2 (nsPush V (.create (child d b) k)).1 !! d =
        some .dir := by
      rw [replay_push]; show (<[child d b := OsNode.file k]> _) !! d = _
      rw [GMap.lookup_insert_ne _ _ (child_ne_self d b)]; exact hd
    have hf : nsReplay (nsPush V (.create (child d b) k)).2 (nsPush V (.create (child d b) k)).1 !!
        child d b = some (.file k) := by
      rw [replay_push]; exact GMap.lookup_insert_eq _ _ _
    iapply wp_osNsOpenCreatExistingG d b k hb _ _ hd' hf _ _ CoPset.subseteq_top $$ Hos HV Hm Hz
    iintro %fd %e %hmo %hres HV Hm Hz Hfd
    iapply HΦ $$ %fd %e Hz
    rcases hres with ⟨rfl, hfd⟩ | ⟨he, rfl⟩
    · ileft
      isplitr; · ipureintro; exact ⟨rfl, hfd⟩
      iexists k
      rw [if_pos rfl]
      iframe
      ipureintro; exact hk
    · iright
      isplitr; · ipureintro; exact ⟨he, rfl⟩
      iexists (some k)
      dsimp only [crStateG]
      iframe
      ipureintro; exact hk

/-- `rename(2)` of the directory `wal.tmp`, in which `seg` is the file of the invariant's key `k`,
onto `wal`, absent, the invariant opened around it. -/
theorem wp_dsRename (dir k : GoString) (γ : GName) (V : NsMap × List NsOp)
    (htd : nsReplay V.2 V.1 !! child dir wtB = some .dir)
    (hts : nsReplay V.2 V.1 !! child (child dir wtB) segB = some (.file k))
    (hw : nsReplay V.2 V.1 !! child dir walB = none) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) dir γ -∗
      osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V -∗ osNsBusy (GF := GF) true -∗
      ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜((e = 0 ∧ V' = nsPush V (.rename (child dir wtB) (child dir walB))) ∨
          (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.rename (child dir wtB) (child dir walB))))) ∧
          (NsOp.rename (child dir wtB) (child dir walB)).apply (nsReplay V.2 V.1) !! child dir wtB =
            none⌝ -∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V' -∗ osNsBusy (GF := GF) false -∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename"
        (Val (PairV (#(child dir wtB)) (#(child dir walB))))) {{ Φ }} := by
  iintro #Hos #Hinv HV Hz Hγ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  unfold dsInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, %ko, >HV1, >Hv, >%Hs, >Hk⟩
  icases osNsAll_agree _ _ V V1 $$ HV HV1 with %he
  subst he
  icases ghostVar_agree _ _ _ _ _ $$ Hγ Hv with %hko
  subst hko
  ihave HVw := (osNsAll_halves V).2 $$ [HV HV1]
  · iframe
  imodintro
  iapply wp_osRenameDirG dir wtB walB wtB_ok walB_ok wt_ne_wal V (safeH_now Hs).1 htd hw
    bootN_disj $$ Hos HVw Hz
  iintro %e %V' %hres HVw Hz
  obtain ⟨hres, h1, h2, h3⟩ := hres
  have hV : V' = V ∨ V' = nsPush V (.rename (child dir wtB) (child dir walB)) := by
    rcases hres with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inr h
    · exact h
  have hs' : SafeH dir (some k) V' :=
    safeH_or_push Hs (safe_rename (safeH_now Hs) htd hts h1 h2 h3) hV
  icases (osNsAll_halves V').1 $$ HVw with ⟨HV, HV1⟩
  imod Hclose $$ [HV1 Hv Hk] with -
  · inext; iexists V', (some k); iframe; ipureintro; exact hs'
  imodintro
  have hfin := And.intro hres (h2 _ (.inl rfl) (not_isUnder_W_T dir))
  iapply HΦ $$ %e %V' %hfin HV Hz Hγ

/-- `rename(2)` of `wal.tmp`, absent, onto `wal` (the retry of a rename that moved it), the
invariant opened around it: it fails. -/
theorem wp_dsRenameAbsent (dir : GoString) (γ : GName) (V : NsMap × List NsOp)
    (hn : nsReplay V.2 V.1 !! child dir wtB = none) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ dsInv (GF := GF) dir γ -∗
      osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V -∗ osNsBusy (GF := GF) true -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V -∗
        osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename"
        (Val (PairV (#(child dir wtB)) (#(child dir walB))))) {{ Φ }} := by
  iintro #Hos #Hinv HV Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod ds_acc dir γ V $$ Hinv HV with ⟨%ko, HV, %Hs, Hclose⟩
  imodintro
  iapply wp_osRenameAbsentG dir wtB walB wtB_ok walB_ok wt_ne_wal V (safeH_now Hs).1 hn bootN_disj
    $$ Hos HV Hz
  iintro %e %he HV Hz
  imod Hclose $$ %V %Hs HV with HV
  imodintro
  iapply HΦ $$ %e %he HV Hz

end steps

/-! ## `os` calls, with the invariant -/

theorem push_ne {V : NsMap × List NsOp} {o : NsOp} : nsPush V o ≠ V := by
  intro h; have := congrArg (fun V => V.2.length) h; simp at this

theorem rm_absent (V : NsMap × List NsOp) (p : GoString) :
    nsReplay (nsPush V (.remove p)).2 (nsPush V (.remove p)).1 !! p = none := by
  rw [replay_push]; exact GMap.lookup_delete_eq _ _

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.Remove(d/b)`, a path whose removal keeps every state `Safe`: removed or not. -/
theorem wp_dsRemove (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : ∀ ko m, Safe dir ko m → NsBelowDir m d)
    (hs : ∀ ko m, Safe dir ko m → Safe dir ko (GMap.delete (child d b) m)) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) dir γ ∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V ∗ osNsBusy (GF := GF) false }}
      (App (Val (@! os.Remove)) (Val #(child d b)))
    {{ (err : GoInterface), RET #err; osNsBusy false ∗ ∃ V',
        osNsAll (DFrac.own (1 : Qp).half) V' ∗ ⌜V' = V ∨ V' = nsPush V (.remove (child d b))⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, HV, Hz⟩
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = V := ⟨_, rfl⟩
  ihave HV : osNsAll (DFrac.own (1 : Qp).half) V1 $$ [HV]
  · subst hV1; iexact HV
  ihave Hp : ⌜V1 = V ∨ V1 = nsPush V (.remove (child d b))⌝ $$ []
  · ipureintro; exact .inl hV1
  clear hV1
  iloeb as IH generalizing %V1 Hp HV Hz
  icases Hp with %Hp
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_dsUnlink dir d b γ hb V1 hd hs $$ Hos Hinv HV Hz as %e %V' %hres HV Hz
  have hV' : V' = V ∨ V' = nsPush V (.remove (child d b)) := by
    rcases Hp with rfl | rfl
    · rcases hres with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
      · exact .inl h
    · rcases hres with ⟨⟨k, hk⟩, -⟩ | ⟨-, h⟩
      · rw [rm_absent] at hk; cases hk
      · exact .inr h
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V' [] HV Hz HΦ
    ipureintro; exact hV'
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hz
    iexists V'
    iframe HV
    ipureintro; exact hV'
  rw [decide_eq_false he0]
  wp_auto
  clear Hp hres
  ihave Hp2 : ⌜V' = V ∨ V' = nsPush V (.remove (child d b))⌝ $$ []
  · ipureintro; exact hV'
  clear hV'
  iloeb as IH2 generalizing %V' Hp2 HV Hz
  icases Hp2 with %hV'
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_dsRmdir dir d b γ hb V' hd hs $$ Hos Hinv HV Hz as %e1 %V2 %hres1 HV Hz
  have hV2 : V2 = V ∨ V2 = nsPush V (.remove (child d b)) := by
    rcases hV' with rfl | rfl
    · rcases hres1 with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
      · exact .inl h
    · rcases hres1 with ⟨hk, -⟩ | ⟨-, h⟩
      · rw [rm_absent] at hk; cases hk
      · exact .inr h
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ %V2 [] HV Hz HΦ
    ipureintro; exact hV2
  rw [decide_eq_false he14]
  wp_auto
  by_cases he10 : e1 = W64 0
  · rw [decide_eq_true he10]
    wp_auto
    iapply HΦ
    iframe Hz
    iexists V2
    iframe HV
    ipureintro; exact hV2
  rw [decide_eq_false he10]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe Hz
    iexists V2
    iframe HV
    ipureintro; exact hV2
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe Hz
    iexists V2
    iframe HV
    ipureintro; exact hV2

/-- `os.Mkdir(d/b, perm)`, a path where a directory keeps every state `Safe`: on success a new
directory, where nothing was, in a directory, nothing below it. -/
theorem wp_dsMkdir' (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : ∀ ko m, Safe dir ko m → NsBelowDir m d)
    (hs : ∀ ko m, Safe dir ko m → Safe dir ko (<[child d b := .dir]> m)) (perm : w32) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) dir γ ∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V ∗ osNsBusy (GF := GF) false }}
      (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
    {{ (err : GoInterface), RET #err; osNsBusy false ∗ ∃ V',
        osNsAll (DFrac.own (1 : Qp).half) V' ∗
        ⌜err = interface.nil → V' = nsPush V (.mkdir (child d b)) ∧
          nsReplay V.2 V.1 !! child d b = none ∧ nsReplay V.2 V.1 !! d = some .dir ∧
          (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, HV, Hz⟩
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = V := ⟨_, rfl⟩
  ihave HV : osNsAll (DFrac.own (1 : Qp).half) V1 $$ [HV]
  · subst hV1; iexact HV
  ihave Hp : ⌜V1 = V ∨ (V1 = nsPush V (.mkdir (child d b)) ∧ nsReplay V.2 V.1 !! child d b = none ∧
      nsReplay V.2 V.1 !! d = some .dir ∧ (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none))⌝ $$ []
  · ipureintro; exact .inl hV1
  clear hV1
  iloeb as IH generalizing %V1 Hp HV Hz
  icases Hp with %Hp
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_dsMkdir dir d b γ hb V1 hd hs $$ Hos Hinv HV Hz as %e %V' %hres HV Hz
  -- the history after the call: `V`, or `V` with the directory made
  have hV' : V' = V ∨ (V' = nsPush V (.mkdir (child d b)) ∧ nsReplay V.2 V.1 !! child d b = none ∧
      nsReplay V.2 V.1 !! d = some .dir ∧ (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none)) := by
    rcases Hp with rfl | ⟨rfl, hp⟩
    · rcases hres with ⟨h1, h2, h3, ⟨-, h⟩ | ⟨-, h | h⟩⟩ | ⟨-, h⟩
      · exact .inr ⟨h, h1, h2, h3⟩
      · exact .inl h
      · exact .inr ⟨h, h1, h2, h3⟩
      · exact .inl h
    · rcases hres with ⟨h1, -⟩ | ⟨-, h⟩
      · rw [replay_push] at h1
        exact absurd h1 (by show (<[child d b := OsNode.dir]> _) !! _ ≠ _; rw [GMap.lookup_insert_eq]; simp)
      · exact .inr ⟨h, hp⟩
  have hok : e = 0 → V' = nsPush V (.mkdir (child d b)) ∧ nsReplay V.2 V.1 !! child d b = none ∧
      nsReplay V.2 V.1 !! d = some .dir ∧ (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none) := by
    intro he
    rcases hV' with rfl | h
    · rcases Hp with rfl | ⟨rfl, -⟩
      · rcases hres with ⟨-, -, -, ⟨-, h⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩
        · exact absurd h (fun h' => push_ne h'.symm)
        · exact absurd he h
        · exact absurd he h
      · rcases hres with ⟨h1, -⟩ | ⟨h, -⟩
        · rw [replay_push] at h1
          exact absurd h1 (by show (<[child d b := OsNode.dir]> _) !! _ ≠ _; rw [GMap.lookup_insert_eq]; simp)
        · exact absurd he h
    · exact h
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V' [] HV Hz HΦ
    ipureintro; exact hV'
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hz
    iexists V'
    iframe HV
    ipureintro; intro _; exact hok he0
  rw [decide_eq_false he0]
  wp_auto
  unfold os.model.pathError
  wp_apply wp_errno
  iapply HΦ
  iframe Hz
  iexists V'
  iframe HV
  ipureintro; intro h; cases h

/-- `Regime(d/b)` in the state of a retried create: `1`. -/
theorem wp_crStateG_regime (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (ko : Option GoString) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ crStateG (child d b) V ko -∗
      (crStateG (child d b) V ko -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "Regime" (Val (#(child d b)))) {{ Φ }} := by
  iintro #Hos Hs HΦ
  cases ko with
  | none =>
    unfold crStateG
    iapply wp_osRegimeG d b hb _ V (.inl hd) CoPset.subseteq_top $$ Hos Hs HΦ
  | some k =>
    unfold crStateG
    icases Hs with ⟨%hk, HV, Hm⟩
    have hd' : NsBelowDir (nsReplay (nsPush V (.create (child d b) k)).2
        (nsPush V (.create (child d b) k)).1) d := by
      left; rw [replay_push]; show (<[child d b := OsNode.file k]> _) !! d = _
      rw [GMap.lookup_insert_ne _ _ (child_ne_self d b)]; exact hd
    iapply wp_osRegimeG d b hb _ _ hd' CoPset.subseteq_top $$ Hos HV
    iintro HV
    iapply HΦ
    dsimp only [crStateG]
    iframe
    ipureintro; exact hk

/-- `os.OpenFile(d/b, O_RDWR|O_CREATE, perm)`, absent from the directory `d` of `V`, a path where
a file keeps every state `Safe`: on success a new file of a fresh key `k`, `d/b` names it. -/
theorem wp_dsOpenCreate (dir d b : GoString) (γ : GName) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (hn : nsReplay V.2 V.1 !! child d b = none)
    (hs : ∀ ko m k, Safe dir ko m → Safe dir ko (<[child d b := .file k]> m)) (perm : w32) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) dir γ ∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V ∗ osNsBusy (GF := GF) false }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osNsBusy false ∗
        ((∃ (fd : w64) (k : GoString), ⌜err = interface.nil ∧ IsInoKey k⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨k, true, true⟩ ∗
            osMeta k (DFrac.own 1) (some newMeta) ∗
            osNsAll (DFrac.own (1 : Qp).half) (nsPush V (.create (child d b) k))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hinv, HV, Hz⟩
  obtain ⟨ko, hko⟩ : ∃ ko : Option GoString, ko = none := ⟨_, rfl⟩
  ihave Hs : crStateG (child d b) V ko $$ [HV]
  · subst hko; unfold crStateG; iexact HV
  clear hko
  iloeb as IH generalizing %ko Hs Hz
  wp_apply wp_crStateG_regime d b hb V hd ko $$ Hos Hs as Hs
  rw [os.file_ty_eq, os.File_ty_eq]
  (try wp_auto)
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  rw [show (W64 66 ||| W64 524288) = flCreat from by decide]
  wp_apply wp_dsCreate_any dir d b γ hb V hd hn hs ko $$ Hos Hinv Hs Hz as %fd %e Hz Hr
  icases Hr with (⟨%he, %k, %hk, HV, Hm, Hfd⟩ | ⟨%he, %ko', Hs⟩)
  · obtain ⟨rfl, -⟩ := he
    rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hz
    ileft
    iexists fd, k
    iframe Hfd Hm HV
    isplitr
    · ipureintro; exact ⟨rfl, hk⟩
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
      iapply IH $$ %ko' Hs Hz HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hz
      iright
      ipureintro; intro h; cases h

/-- `os.Rename(dir/wal.tmp, dir/wal)`, `wal.tmp` a directory in which `seg` is the file of the
invariant's key `k`, `wal` absent: on success renamed. -/
theorem wp_dsRenameWal (dir k : GoString) (γ : GName) (V : NsMap × List NsOp)
    (htd : nsReplay V.2 V.1 !! child dir wtB = some .dir)
    (hts : nsReplay V.2 V.1 !! child (child dir wtB) segB = some (.file k))
    (hw : nsReplay V.2 V.1 !! child dir walB = none) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) dir γ ∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V ∗ osNsBusy (GF := GF) false ∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) }}
      (App (App (Val (@! os.Rename)) (Val #(child dir wtB))) (Val #(child dir walB)))
    {{ (err : GoInterface), RET #err; osNsBusy false ∗ ghostVar γ (1 : Qp).half (some k) ∗
        ∃ V', osNsAll (DFrac.own (1 : Qp).half) V' ∗
          ⌜err = interface.nil → V' = nsPush V (.rename (child dir wtB) (child dir walB))⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, HV, Hz, Hγ⟩
  imod ds_allDir dir γ V $$ Hinv HV with ⟨HV, %hdir⟩
  wp_apply wp_osNsLstatDirG dir walB walB_ok _ V (AllDir.now hdir) hw CoPset.subseteq_top
    $$ Hos HV as %e0 HV
  (try wp_auto)
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = V := ⟨_, rfl⟩
  ihave HV : osNsAll (DFrac.own (1 : Qp).half) V1 $$ [HV]
  · subst hV1; iexact HV
  ihave Hp : ⌜V1 = V ∨ (V1 = nsPush V (.rename (child dir wtB) (child dir walB)) ∧
      nsReplay V1.2 V1.1 !! child dir wtB = none)⌝ $$ []
  · ipureintro; exact .inl hV1
  clear hV1
  iloeb as IH generalizing %V1 Hp HV Hz Hγ
  icases Hp with %Hp
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  rcases Hp with rfl | ⟨rfl, hT⟩
  · wp_apply wp_dsRename dir k γ V1 htd hts hw $$ Hos Hinv HV Hz Hγ as %e %V' %hres HV Hz Hγ
    obtain ⟨hres, hT⟩ := hres
    have hV' : V' = V1 ∨ (V' = nsPush V1 (.rename (child dir wtB) (child dir walB)) ∧
        nsReplay V'.2 V'.1 !! child dir wtB = none) := by
      rcases hres with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
      · exact .inr ⟨rfl, by rw [replay_push]; exact hT⟩
      · exact .inl rfl
      · exact .inr ⟨rfl, by rw [replay_push]; exact hT⟩
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ %V' [] HV Hz Hγ HΦ
      ipureintro; exact hV'
    rw [decide_eq_false he4]
    wp_auto
    by_cases he0 : e = W64 0
    · rw [decide_eq_true he0]
      wp_auto
      iapply HΦ
      iframe Hz Hγ
      iexists V'
      iframe HV
      ipureintro; intro _
      rcases hres with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd he0 h
    rw [decide_eq_false he0]
    wp_auto
    wp_apply wp_errno
    unfold os.model.linkError
    rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
    wp_auto
    iapply HΦ
    iframe Hz Hγ
    iexists V'
    iframe HV
    ipureintro; intro h; cases h
  · wp_apply wp_dsRenameAbsent dir γ _ hT $$ Hos Hinv HV Hz as %e %he HV Hz
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ %_ [] HV Hz Hγ HΦ
      ipureintro; exact .inr ⟨rfl, hT⟩
    rw [decide_eq_false he4]
    wp_auto
    rw [decide_eq_false (show ¬ e = W64 0 from he)]
    wp_auto
    wp_apply wp_errno
    unfold os.model.linkError
    rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
    wp_auto
    iapply HΦ
    iframe Hz Hγ
    iexists _
    iframe HV
    ipureintro; intro h; cases h

end oscalls

/-! ## The program -/

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem wabs_delete {dir p : GoString} {V : NsMap × List NsOp} (h : WAbs dir V)
    (hp : p ≠ child dir walB) {V' : NsMap × List NsOp} (hV : V' = V ∨ V' = nsPush V (.remove p)) :
    WAbs dir V' := by
  rcases hV with rfl | rfl
  · exact h
  · exact wabs_push h (by
      show (GMap.delete p _) !! _ = none
      rw [GMap.lookup_delete_ne _ hp]; exact wabs_now h)

/-- `Create(dir)`, `dir` a directory, `wal` absent from every prefix of the history: it does not
panic. -/
theorem wp_Create (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (dir : GoString) (γ : GName) (V : NsMap × List NsOp) (ko : Option GoString)
    (hw : WAbs dir V) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) dir γ ∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) V ∗ osNsBusy (GF := GF) false ∗
        ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Create)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, HV, Hz, Hγ⟩
  (try wp_auto)
  try rw [show dir ++ go!"/wal.tmp" = child dir wtB from rfl]
  try rw [show child dir wtB ++ go!"/seg" = child (child dir wtB) segB from rfl]
  -- `Remove(tmp/seg)`
  wp_apply wp_dsRemove dir (child dir wtB) segB γ segB_ok V
      (fun _ _ h => .inr ⟨dir, wtB, wtB_ok, rfl, h.1⟩)
      (fun _ _ h => safe_delete h (child_child_ne _ _ _) (Ts_ne_W dir) (Ts_ne_Ws dir))
      $$ [Hos Hinv HV Hz] as %err1 ⟨Hz, %V1, HV, %hV1⟩
  · iframe; iframe #
  have hw1 : WAbs dir V1 := wabs_delete hw (Ts_ne_W dir) hV1
  (try wp_auto)
  -- `Remove(tmp)`
  wp_apply wp_dsRemove dir dir wtB γ wtB_ok V1 (fun _ _ h => .inl h.1)
      (fun _ _ h => safe_delete h (child_ne_self _ _) (T_ne_W dir) (T_ne_Ws dir))
      $$ [Hos Hinv HV Hz] as %err2 ⟨Hz, %V2, HV, %hV2⟩
  · iframe; iframe #
  have hw2 : WAbs dir V2 := wabs_delete hw1 (T_ne_W dir) hV2
  (try wp_auto)
  -- `Mkdir(tmp)`
  wp_apply wp_dsMkdir' dir dir wtB γ wtB_ok V2 (fun _ _ h => .inl h.1)
      (fun _ _ h => safe_insert_dir h (child_ne_self _ _) (T_ne_W dir) (T_ne_Ws dir)) (W32 488)
      $$ [Hos Hinv HV Hz] as %err3 ⟨Hz, %V3, HV, %hV3⟩
  · iframe; iframe #
  cases err3 with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  obtain ⟨rfl, hTn, -, hunder⟩ := hV3 rfl
  have hw3 : WAbs dir (nsPush V2 (.mkdir (child dir wtB))) := wabs_push hw2 (by
    show (<[child dir wtB := OsNode.dir]> _) !! _ = none
    rw [GMap.lookup_insert_ne _ _ (T_ne_W dir)]; exact wabs_now hw2)
  have hT3 : nsReplay (nsPush V2 (.mkdir (child dir wtB))).2 (nsPush V2 (.mkdir (child dir wtB))).1 !!
      child dir wtB = some .dir := by
    rw [replay_push]; exact GMap.lookup_insert_eq _ _ _
  have hTs3 : nsReplay (nsPush V2 (.mkdir (child dir wtB))).2 (nsPush V2 (.mkdir (child dir wtB))).1 !!
      child (child dir wtB) segB = none := by
    rw [replay_push]; show (<[child dir wtB := OsNode.dir]> _) !! _ = none
    rw [GMap.lookup_insert_ne _ _ (Ts_ne_T dir).symm]; exact hunder segB
  generalize hV3e : nsPush V2 (.mkdir (child dir wtB)) = V3 at hw3 hT3 hTs3
  (try wp_auto)
  -- `OpenFile(tmp/seg, O_RDWR|O_CREATE)`
  rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
  rw [show child dir wtB ++ go!"/seg" = child (child dir wtB) segB from rfl]
  wp_apply wp_dsOpenCreate dir (child dir wtB) segB γ segB_ok V3 hT3 hTs3
      (fun _ _ _ h => safe_insert_file h (child_child_ne _ _ _) (Ts_ne_T dir) (Ts_ne_W dir)
        (Ts_ne_Ws dir)) (W32 438)
      $$ [Hos Hinv HV Hz] as %f %err ⟨Hz, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%fd, %k, %hek, Hf, Hfd, Hm, HV⟩ | %herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hk⟩ := hek
  (try wp_auto)
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  ihave Hb0 : osBytes k (min (W64 0).toNat newMeta.size) (DFrac.own 1) [] $$ []
  · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
  ihave Hmc : mcellsAny newMeta.maps (min (W64 0).toNat newMeta.size) ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny newMeta; iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_WriteAt f fd (child (child dir wtB) segB) (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0)
      (DFrac.own 1) ⟨k, true, true⟩ 1 newMeta [] rfl (by decide) (by decide) (by decide)
      (by simp [newMeta]) (fun _ => rfl) $$ [Hos Hf Hsl Hfd Hm Hb0 Hmc]
    as %n %err ⟨Hf, Hsl, Hfd, %j, %ys, %h, %Hres, Hm, Hys, -⟩
  · iframe; iexact Hos
  obtain ⟨hj, hys, -, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  have hys' : ys.map Prod.fst = dataC := by rw [hys]; exact pwBytes_data
  rw [show pwSize 0 0 dataC.length = 8 from rfl, show min 0 0 = 0 from rfl]
  generalize hm1 : (⟨8, 0, h, false, true, ∅, [], 0⟩ : OsMeta) = m1
  have hm1ok : m1.ok = true := by rw [← hm1]
  have hm1sz : m1.size = 8 := by rw [← hm1]
  clear hm1
  dsimp only
  (try wp_auto)
  -- `f.Sync()`
  wp_apply wp_Sync f fd (child (child dir wtB) segB) (DFrac.own 1) (DFrac.own 1) ⟨k, true, true⟩ _ 0 ys
    $$ [Hos Hf Hfd Hm Hys] as %err ⟨Hf, Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm, Hys⟩ | ⟨%he, -, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  subst he
  (try wp_auto)
  wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; iexact Hos
  (try wp_auto)
  -- the file, durable, goes into the invariant under the key `k`
  have hw4 : WAbs dir (nsPush V3 (.create (child (child dir wtB) segB) k)) := wabs_push hw3 (by
    show (<[child (child dir wtB) segB := OsNode.file k]> _) !! _ = none
    rw [GMap.lookup_insert_ne _ _ (Ts_ne_W dir)]; exact wabs_now hw3)
  have hT4 : nsReplay (nsPush V3 (.create (child (child dir wtB) segB) k)).2
      (nsPush V3 (.create (child (child dir wtB) segB) k)).1 !! child dir wtB = some .dir := by
    rw [replay_push]; show (<[child (child dir wtB) segB := OsNode.file k]> _) !! _ = _
    rw [GMap.lookup_insert_ne _ _ (Ts_ne_T dir)]; exact hT3
  have hTs4 : nsReplay (nsPush V3 (.create (child (child dir wtB) segB) k)).2
      (nsPush V3 (.create (child (child dir wtB) segB) k)).1 !! child (child dir wtB) segB =
        some (.file k) := by
    rw [replay_push]; exact GMap.lookup_insert_eq _ _ _
  generalize hV4e : nsPush V3 (.create (child (child dir wtB) segB) k) = V4 at hw4 hT4 hTs4
  icases (osMeta_halves k _).1 $$ Hm with ⟨Hm, Hmi⟩
  icases (osBytes_halves k 0 _).1 $$ Hys with ⟨Hys, Hysi⟩
  ihave Hk : keyRes (L := hG.goose_localGS) (some k) $$ [Hmi Hysi]
  · unfold keyRes
    iexists _, _
    iframe Hmi Hysi
    ipureintro; exact synced_good m1 hm1ok hm1sz ys hys'
  imod ds_deposit dir γ V4 ko k hw4 $$ Hinv HV Hγ Hk with ⟨HV, Hγ⟩
  -- `Rename(tmp, dir/wal)`
  try rw [show dir ++ go!"/wal" = child dir walB from rfl]
  wp_apply wp_dsRenameWal dir k γ V4 hT4 hTs4 (wabs_now hw4) $$ [Hos Hinv HV Hz Hγ]
    as %err ⟨Hz, Hγ, %V5, HV, %hV5⟩
  · iframe; iframe #
  cases err with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  (try wp_auto)
  -- the directory's sync
  imod ds_allDir dir γ V5 $$ Hinv HV with ⟨HV, %had⟩
  ihave Hd := osNsAll_dir (L := hG.goose_localGS) _ V5 dir had $$ HV
  wp_apply wp_syncDir dir _ _ $$ [Hos Hd] as %ok Hd
  · iframe; iexact Hos
  (try wp_auto)
  iapply HΦ
  itrivial

end prog

/-! ## Boot -/

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem osNsAll_split (q1 q2 : Qp) (V : NsMap × List NsOp) :
    osNsAll (GF := GF) (DFrac.own (q1 + q2)) V ⊣⊢
      osNsAll (GF := GF) (DFrac.own q1) V ∗ osNsAll (GF := GF) (DFrac.own q2) V :=
  gElem_split _ _ () q1 q2 V

/-- `readNames(d)`, with a fraction of the history `V`, `d` a directory in every prefix of it: the
names of `d` now, each once, or `ok = false`. -/
theorem wp_readNamesG (d : GoString) (q : Qp) (V : NsMap × List NsOp) (hd : AllDir V d) :
    {{ osInv (GF := GF) ∗ osNsAll (GF := GF) (DFrac.own q) V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readNames)) (Val #d))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); osNsAll (DFrac.own q) V ∗
        (⌜ok = false⌝ ∨ ∃ names : List GoString, ⌜ok = true ∧ names.Nodup ∧
          ∀ b, b ∈ names ↔ (entsOf (nsReplay V.2 V.1) d !! b).isSome⌝ ∗ sl ↦* names) }} := by
  iintro %Φ ⟨#Hos, HV⟩ HΦ
  rw [← Qp.half_add_half q]
  icases (osNsAll_split q.half q.half V).1 $$ HV with ⟨H1, H2⟩
  ihave Hd := osNsAll_dir (L := hG.goose_localGS) (DFrac.own q.half) V d hd $$ H1
  wp_apply wp_readNames d q.half _ $$ [Hos Hd] as %sl %ok ⟨Hd, Hr⟩
  · iframe; iexact Hos
  unfold osDir
  icases Hd with ⟨%V', H1, %hg⟩
  icases osNsAll_agree _ _ V V' $$ H2 H1 with %he
  subst he
  ihave HV := (osNsAll_split q.half q.half V).2 $$ [H1 H2]
  · iframe
  rw [Qp.half_add_half q]
  iapply HΦ
  iframe HV
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · ileft; ipureintro; exact hok
  · iright; iexists names; iframe Hsl; ipureintro
    obtain ⟨h1, h2, h3⟩ := hn
    refine ⟨h1, h2, fun b => ?_⟩
    rw [h3 b, dview_now]

/-- `checkDir(w)`, `w` a directory in every prefix of the history `V`, its `seg` the file of `k`,
of which the program has half, `CheckOk`: it does not panic. -/
theorem wp_checkDir (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (w k : GoString) (q : Qp) (V : NsMap × List NsOp) (hw : AllDir V w)
    (hk : nsReplay V.2 V.1 !! child w segB = some (.file k))
    (mo : Option OsMeta) (bs : List (w8 × Bool)) (hok : CheckOk mo bs) :
    {{ osInv (GF := GF) ∗ osNsAll (GF := GF) (DFrac.own q) V ∗
        osMeta (GF := GF) k (DFrac.own (1 : Qp).half) mo ∗
        osBytes (GF := GF) k 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.checkDir)) (Val #w))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, HV, Hm, Hb⟩
  (try wp_auto)
  wp_apply wp_readNamesG w q V hw $$ [Hos HV] as %sl %ok ⟨HV, Hr⟩
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
      ihave Hd := osNsAll_dir (L := hG.goose_localGS) (DFrac.own q) V w hw $$ HV
      wp_apply wp_check wp_ReadAt wp_Close w k _ _
          (by rw [dview_now, entsOf_child _ _ _ segB_ok]; exact hk) mo bs hok
        $$ [Hos Hd Hm Hb]
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
    rw [hmem, if_pos segB_ok]; show (nsReplay V.2 V.1 !! child w segB).isSome = true; rw [hk]; rfl

/-- `BootDir(dir)`, from a history with nothing logged whose namespace is `Safe` with the
invariant's key `ko0`, of whose file the program has half (`segRes`): it does not panic. -/
theorem wp_BootDir (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (dir : GoString) (γ : GName) (ns : NsMap) (ko0 : Option GoString) (hs : Safe dir ko0 ns) :
    {{ osInv (GF := GF) ∗ dsInv (GF := GF) dir γ ∗
        osNsAll (GF := GF) (DFrac.own (1 : Qp).half) (ns, []) ∗ osNsBusy (GF := GF) false ∗
        ghostVar (GF := GF) γ (1 : Qp).half ko0 ∗ segRes ko0 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.BootDir)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, HV, Hz, Hγ, Hs⟩
  have hall : ∀ x, ns !! x = some .dir → AllDir (ns, []) x := fun x hx n => by
    show nsReplay (([] : List NsOp).take n) ns !! x = _
    simp only [List.take_nil]; exact hx
  (try wp_auto)
  wp_apply wp_readNamesG dir (1 : Qp).half (ns, []) (hall dir hs.1) $$ [Hos HV]
    as %sl %ok ⟨HV, Hr⟩
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
      have hW : (ns !! child dir walB).isSome := by
        have := (hmem walB).1 (List.mem_of_getElem? hb)
        rw [if_pos walB_ok] at this; exact this
      have hWd : ns !! child dir walB = some .dir := by
        cases h : ns !! child dir walB with
        | none => rw [h] at hW; cases hW
        | some x =>
          cases x with
          | dir => rfl
          | file k => exact absurd h (hs.2.2.1 k)
      obtain ⟨k, rfl, hk⟩ := hs.2.2.2 hWd
      unfold segRes
      icases Hs with ⟨%mo, %bs, Hm, Hb, %hok⟩
      try rw [show dir ++ go!"/wal" = child dir walB from rfl]
      wp_apply wp_checkDir wp_ReadAt wp_Close (child dir walB) k _ (ns, []) (hall _ hWd) hk mo bs hok
        $$ [Hos HV Hm Hb]
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
    have hWn : ns !! child dir walB = none := by
      cases h : ns !! child dir walB with
      | none => rfl
      | some x =>
        exact absurd ((hmem walB).2 (by rw [if_pos walB_ok]; show (ns !! child dir walB).isSome = true; rw [h]; rfl)) hns
    (try wp_auto)
    wp_apply wp_Create wp_Close wp_WriteAt wp_Sync dir γ (ns, []) ko0 (wabs_nil dir ns hWn)
      $$ [Hos Hinv HV Hz Hγ]
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial

end boot

end osfs_walfs
end EtcdGrove
end Perennial

end
