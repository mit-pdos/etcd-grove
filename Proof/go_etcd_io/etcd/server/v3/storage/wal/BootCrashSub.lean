/- Lean-first (no Rocq counterpart).

# The crash boot's claims, pure (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log", (b))

`walBootCrash` (`BootCrash.lean`) splits the whole claims the shared mode's switch gives the program
(one per directory of the crashed tree `m`, with nothing logged) into what `walInv_alloc` and
`walAreaRes` take, and gives the rest back. This module has the pure side:

* **the descendants of a directory** (`TDesc m J K`): in a well-formed tree (`TreeWf`) the trees
  under two entries of the area are disjoint (`tDesc_area_uniq`: unique naming, no entry naming a
  root);
* **the area's names**: the WALs found (`bootWals`, `BootCrashCl`), the names `nm.<sfx>` holding a
  directory with every directory under each (`bootSubs`: what `walAreaRes`'s `SubCover` needs, tagged
  with the name), the names that are no `AreaSlot` holding an entry (`bootOthers`: given back), the
  area claim's names (`bootN`: all but those and the WALs' names, which have claims of their own);
* **the directories taken** (`bootTaken`: the area's, the WALs', those under an `nm.<sfx>`; distinct)
  and the others (`bootRest`: given back);
* **the files-only premise** (`BootFo`, the ledger's `hfo`, 2026-11-14): every WAL directory holds only
  files (from `walInv_crash`: `bootFo_of`). Its `nm.tmp` parts went on 2026-11-22: `Create` copes with
  whatever a crash left at `nm.tmp` (`tmpAny`), the boot hands its claims over ranked (`bootCls_ranked`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrashCl
public import Proof.os.RemoveAllCover

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- A list's map has no duplicate if the list has none and the map is injective on it. -/
theorem _root_.List.Nodup.mapOnW {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hn, H => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, List.Nodup.mapOnW (List.nodup_cons.1 hn).2
      (fun x hx y hy => H x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    have := H b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e
    subst this
    exact (List.nodup_cons.1 hn).1 hb

/-! ## Names -/

/-- A name `nm.sfx` is no WAL name (it holds a `.`). -/
theorem sfx_not_walName' (nm sfx : GoString) : ¬ walNameOk (nm ++ go!"." ++ sfx) := by
  intro hw; apply hw.2.2; simp

theorem tmpName_not_walName' (nm : GoString) : ¬ walNameOk (tmpName nm) := by
  intro hw; apply hw.2.2; simp [tmpName]

theorem tmpName_areaSlot' {nm : GoString} (h : walNameOk nm) : AreaSlot (tmpName nm) :=
  ⟨nm, h, .inr ⟨go!"tmp", by simp [tmpName]⟩⟩

/-- A WAL name is an area slot. -/
theorem areaSlot_walName {nm : GoString} (h : walNameOk nm) : AreaSlot nm := ⟨nm, h, Or.inl rfl⟩

/-- A WAL name is none of `BootTake`'s temporary directories: the files taken from its directory are
those at its non-`.wal` names. -/
theorem bootTake_wal {a b : GoString} (ha : walNameOk a) : BootTake a b ↔ walNameP b = false := by
  constructor
  · exact bootTake_not_wal
  · intro hb; exact .inl ⟨ha, hb⟩

/-! ## Descendants -/

/-- **`K` is `J` or a directory under it**, in the tree `m`. -/
inductive TDesc (m : Tree) (J : Ino) : Ino → Prop where
  | refl : TDesc m J J
  | step (K : Ino) (b : GoString) (K' : Ino) : TDesc m J K → m.entry K b = some (.dir K') → TDesc m J K'

/-- Under unique naming, two directories above one are one above the other. -/
theorem tDesc_forest {m : Tree} (hu : UniqNames m) {J J' K : Ino} (h : TDesc m J K)
    (h' : TDesc m J' K) : TDesc m J J' ∨ TDesc m J' J := by
  induction h generalizing J' with
  | refl => exact .inr h'
  | step K b K' hd he ih =>
    cases h' with
    | refl => exact .inl (.step K b K' hd he)
    | step K1 b1 _ hd1 he1 =>
      have e := (hu _ _ _ _ _ he he1).1
      subst e
      exact ih hd1

/-- Nothing is above a root but itself (no entry names a root's directory). -/
theorem tDesc_root {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString} {jr : Ino}
    (hr : (r, jr) ∈ R) {J : Ino} (h : TDesc m J jr) : J = jr := by
  cases h with
  | refl => rfl
  | step K b _ _ he => exact (hw.2.2.2.1 _ _ _ he r hr).elim

/-- **The trees under two entries of a root are disjoint.** -/
theorem tDesc_area_uniq {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) {a1 a2 : GoString} {J1 J2 K : Ino}
    (h1 : m.entry jr a1 = some (.dir J1)) (h2 : m.entry jr a2 = some (.dir J2))
    (d1 : TDesc m J1 K) (d2 : TDesc m J2 K) : a1 = a2 := by
  have hu := uniqNames_of_wf hw
  -- one above the other: then they are one
  have key : ∀ {a a' : GoString} {J J' : Ino}, m.entry jr a = some (.dir J) →
      m.entry jr a' = some (.dir J') → TDesc m J J' → a = a' := by
    intro a a' J J' he he' d
    cases d with
    | refl => exact (hu _ _ _ _ _ he he').2
    | step K b _ dK heK =>
      have e := (hu _ _ _ _ _ heK he').1
      subst e
      have e2 := tDesc_root hw hr dK
      subst e2
      exact (hw.2.2.2.1 _ _ _ he r hr).elim
  rcases tDesc_forest hu d1 d2 with d | d
  · exact key h1 h2 d
  · exact (key h2 h1 d).symm

/-- A directory under one of the tree's is one of the tree's. -/
theorem tDesc_mem {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {J K : Ino} (hJ : J ∈ m)
    (h : TDesc m J K) : K ∈ m := by
  induction h with
  | refl => exact hJ
  | step K b K' _ he _ => exact (hw.2.2.1 _ _ _ he).2 K' (List.mem_singleton_self _)

/-- Under a directory of files only there is nothing but itself. -/
theorem tDesc_filesOnly {m : Tree} {J K : Ino} (hfo : FilesOnly (entsOf m J)) (h : TDesc m J K) :
    K = J := by
  induction h with
  | refl => rfl
  | step K b K' _ he ih =>
    subst ih
    obtain ⟨i, hi⟩ := hfo b _ (by rw [entsOf_lookup]; exact he)
    cases hi

/-! ## The area's names -/

/-- A name `nm.<sfx>` of the area (an `AreaSlot` that is no WAL name). -/
def SubSlot (a : GoString) : Prop := AreaSlot a ∧ ¬ walNameOk a

open Classical in
/-- The directories under the area's entry `an`, tagged with its name, if it is an `nm.<sfx>`. -/
def bootSubsF (m : Tree) (an : GoString × Node) : List (GoString × Ino) :=
  match an.2 with
  | .dir J => if SubSlot an.1 then
      (((GMap.toList m).map (·.1)).filter (fun j => decide (TDesc m J j))).map (fun j => (an.1, j))
    else []
  | .file _ => []

/-- **The directories under each `nm.<sfx>` of the area**, tagged with the name. -/
def bootSubs (m : Tree) (jr : Ino) : List (GoString × Ino) :=
  (GMap.toList (entsOf m jr)).flatMap (bootSubsF m)

theorem bootSubsF_fst {m : Tree} {bn : GoString × Node} {z : GoString × Ino} (hz : z ∈ bootSubsF m bn) :
    z.1 = bn.1 := by
  classical
  obtain ⟨b, n⟩ := bn
  unfold bootSubsF at hz
  cases n with
  | file _ => cases hz
  | dir J =>
    simp only at hz
    split at hz
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz; rfl
    · cases hz

theorem mem_dom {m : Tree} {j : Ino} : j ∈ (GMap.toList m).map (·.1) ↔ j ∈ m := by
  constructor
  · intro h
    obtain ⟨⟨j', d⟩, hm, rfl⟩ := List.mem_map.1 h
    exact (GMap.mem_iff _ _).2 (by rw [(GMap.mem_toList _ _ _).1 hm]; rfl)
  · intro h
    cases he : m !! j with
    | none => have := (GMap.mem_iff _ _).1 h; rw [he] at this; cases this
    | some d => exact List.mem_map.2 ⟨(j, d), (GMap.mem_toList _ _ _).2 he, rfl⟩

theorem dom_nodup (m : Tree) : ((GMap.toList m).map (·.1)).Nodup := GMap.toList_keys_nodup m

open Classical in
theorem mem_bootSubs {m : Tree} {jr : Ino} {a : GoString} {j : Ino} :
    (a, j) ∈ bootSubs m jr ↔ SubSlot a ∧ ∃ J, m.entry jr a = some (.dir J) ∧ TDesc m J j ∧ j ∈ m := by
  unfold bootSubs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨a', n⟩, hm, hj⟩
    unfold bootSubsF at hj
    have he := (GMap.mem_toList _ _ _).1 hm
    rw [entsOf_lookup] at he
    cases n with
    | file _ => cases hj
    | dir J =>
      simp only at hj
      split at hj
      · next hs =>
        obtain ⟨j', hj', e⟩ := List.mem_map.1 hj
        cases e
        obtain ⟨hd, hD⟩ := List.mem_filter.1 hj'
        exact ⟨hs, J, he, of_decide_eq_true hD, mem_dom.1 hd⟩
      · cases hj
  · rintro ⟨hs, J, he, hD, hj⟩
    refine ⟨(a, .dir J), (GMap.mem_toList _ _ _).2 (by rw [entsOf_lookup]; exact he), ?_⟩
    unfold bootSubsF
    simp only
    rw [if_pos hs]
    exact List.mem_map.2 ⟨j, List.mem_filter.2 ⟨mem_dom.2 hj, decide_eq_true hD⟩, rfl⟩

/-- **A directory is under one `nm.<sfx>` only.** -/
theorem bootSubs_fun {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString} {jr : Ino}
    (hr : (r, jr) ∈ R) {a a' : GoString} {j : Ino} (h : (a, j) ∈ bootSubs m jr)
    (h' : (a', j) ∈ bootSubs m jr) : a = a' := by
  obtain ⟨-, J, he, hd, -⟩ := mem_bootSubs.1 h
  obtain ⟨-, J', he', hd', -⟩ := mem_bootSubs.1 h'
  exact tDesc_area_uniq hw hr he he' hd hd'

theorem bootSubs_nodup (m : Tree) (jr : Ino) : (bootSubs m jr).Nodup := by
  classical
  unfold bootSubs
  refine nodup_flatMap_of (toList_nodup _) (fun an _ => ?_) (fun an han an' han' z hz hz' => ?_)
  · obtain ⟨a, n⟩ := an
    unfold bootSubsF
    cases n with
    | file _ => exact List.nodup_nil
    | dir J =>
      simp only
      split
      · exact List.Nodup.mapOnW ((dom_nodup m).filter _) (fun x _ y _ e => (Prod.mk.inj e).2)
      · exact List.nodup_nil
  · have e1 := bootSubsF_fst hz
    have e2 := bootSubsF_fst hz'
    have h1 := (GMap.mem_toList _ _ _).1 han
    have h2 := (GMap.mem_toList _ _ _).1 han'
    obtain ⟨a, n⟩ := an
    obtain ⟨a', n'⟩ := an'
    simp only at e1 e2 h1 h2
    subst e1
    rw [← e2] at h2
    rw [h1] at h2
    cases h2; rw [e2]

open Classical in
/-- The area's names holding an entry that are no `AreaSlot` (given back to the program). -/
def bootOthers (m : Tree) (jr : Ino) : List GoString :=
  ((GMap.toList (entsOf m jr)).map (·.1)).filter (fun b => decide (¬ AreaSlot b))

open Classical in
theorem mem_bootOthers {m : Tree} {jr : Ino} {b : GoString} :
    b ∈ bootOthers m jr ↔ ¬ AreaSlot b ∧ ∃ n, m.entry jr b = some n := by
  unfold bootOthers
  rw [List.mem_filter]
  constructor
  · rintro ⟨hm, hs⟩
    obtain ⟨⟨b', n⟩, hb, rfl⟩ := List.mem_map.1 hm
    refine ⟨of_decide_eq_true hs, n, ?_⟩
    rw [← entsOf_lookup]; exact (GMap.mem_toList _ _ _).1 hb
  · rintro ⟨hs, n, he⟩
    refine ⟨List.mem_map.2 ⟨(b, n), (GMap.mem_toList _ _ _).2 (by rw [entsOf_lookup]; exact he), rfl⟩,
      decide_eq_true hs⟩

/-- The WALs' names. -/
def bootWn (m : Tree) (jr : Ino) : List GoString := (bootWals m jr).map (·.1)

theorem bootWn_nodup (m : Tree) (jr : Ino) : (bootWn m jr).Nodup :=
  List.Nodup.mapOnW (bootWals_nodup m jr) (fun x hx y hy e => by
    obtain ⟨a, J⟩ := x
    obtain ⟨a', J'⟩ := y
    simp only at e
    subst e
    rw [bootWals_fun hx hy])

theorem mem_bootWn {m : Tree} {jr : Ino} {nm : GoString} :
    nm ∈ bootWn m jr ↔ ∃ J, (nm, J) ∈ bootWals m jr := by
  unfold bootWn
  constructor
  · intro h; obtain ⟨⟨a, J⟩, hm, rfl⟩ := List.mem_map.1 h; exact ⟨J, hm⟩
  · rintro ⟨J, h⟩; exact List.mem_map.2 ⟨_, h, rfl⟩

/-- **The area claim's names**: all but the WALs' and those given back. -/
def bootN (m : Tree) (jr : Ino) : NameSet := .except (bootOthers m jr ++ bootWn m jr)

theorem bootN_walName {m : Tree} {jr : Ino} {nm : GoString} (h : walNameOk nm) :
    (bootN m jr).Mem nm ∨ nm ∈ bootWn m jr := by
  by_cases hw : nm ∈ bootWn m jr
  · exact .inr hw
  · refine .inl (fun hm => ?_)
    rcases List.mem_append.1 hm with ho | hw'
    · exact (mem_bootOthers.1 ho).1 (areaSlot_walName h)
    · exact hw hw'

theorem bootN_sfx {m : Tree} {jr : Ino} (nm sfx : GoString) (h : walNameOk nm) :
    (bootN m jr).Mem (nm ++ go!"." ++ sfx) := by
  intro hm
  rcases List.mem_append.1 hm with ho | hw
  · exact (mem_bootOthers.1 ho).1 ⟨nm, h, .inr ⟨sfx, rfl⟩⟩
  · obtain ⟨J, hJ⟩ := mem_bootWn.1 hw
    exact sfx_not_walName' nm sfx (mem_bootWals.1 hJ).1

theorem bootN_tmp {m : Tree} {jr : Ino} {nm : GoString} (h : walNameOk nm) :
    (bootN m jr).Mem (tmpName nm) := by
  intro hm
  rcases List.mem_append.1 hm with ho | hw
  · exact (mem_bootOthers.1 ho).1 (tmpName_areaSlot' h)
  · obtain ⟨J, hJ⟩ := mem_bootWn.1 hw
    exact tmpName_not_walName' nm (mem_bootWals.1 hJ).1

/-- A name of the area claim holding a directory, no WAL name, is an `nm.<sfx>`. -/
theorem bootN_subSlot {m : Tree} {jr : Ino} {b : GoString} {J : Ino} (hb : (bootN m jr).Mem b)
    (hw : ¬ walNameOk b) (he : m.entry jr b = some (.dir J)) : SubSlot b := by
  refine ⟨Classical.byContradiction (fun hs => hb (List.mem_append.2 (.inl ?_))), hw⟩
  exact mem_bootOthers.2 ⟨hs, _, he⟩

/-! ## The directories taken -/

/-- **The directories the crash boot takes**: the area's, the WALs', those under an `nm.<sfx>`. -/
def bootTaken (m : Tree) (jr : Ino) : List Ino :=
  jr :: ((bootWals m jr).map (·.2) ++ (bootSubs m jr).map (·.2))

theorem bootWals_snd_nodup {m : Tree} (hu : UniqNames m) (jr : Ino) :
    ((bootWals m jr).map (·.2)).Nodup :=
  List.Nodup.mapOnW (bootWals_nodup m jr) (fun x hx y hy e => by
    obtain ⟨a, J⟩ := x
    obtain ⟨a', J'⟩ := y
    simp only at e
    subst e
    rw [bootWals_inj hu hx hy])

theorem bootSubs_snd_nodup {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) : ((bootSubs m jr).map (·.2)).Nodup :=
  List.Nodup.mapOnW (bootSubs_nodup m jr) (fun x hx y hy e => by
    obtain ⟨a, j⟩ := x
    obtain ⟨a', j'⟩ := y
    simp only at e
    subst e
    rw [bootSubs_fun hw hr hx hy])

theorem bootSubs_ne_root {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) {a : GoString} (h : (a, jr) ∈ bootSubs m jr) : False := by
  obtain ⟨-, J, he, hd, -⟩ := mem_bootSubs.1 h
  have e := tDesc_root hw hr hd
  subst e
  exact hw.2.2.2.1 _ _ _ he r hr

theorem bootWals_not_sub {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) {nm a : GoString} {J : Ino} (h : (nm, J) ∈ bootWals m jr)
    (h' : (a, J) ∈ bootSubs m jr) : False := by
  obtain ⟨hn, he⟩ := mem_bootWals.1 h
  obtain ⟨⟨-, hs⟩, J', he', hd, -⟩ := mem_bootSubs.1 h'
  have e := tDesc_area_uniq hw hr he he' .refl hd
  subst e
  exact hs hn

theorem bootTaken_nodup {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) : (bootTaken m jr).Nodup := by
  have hu := uniqNames_of_wf hw
  unfold bootTaken
  refine List.nodup_cons.2 ⟨fun hm => ?_, List.nodup_append.2 ⟨bootWals_snd_nodup hu jr,
    bootSubs_snd_nodup hw hr, fun x hx y hy e => ?_⟩⟩
  · rcases List.mem_append.1 hm with h | h
    · obtain ⟨⟨a, J⟩, hJ, e⟩ := List.mem_map.1 h
      simp only at e; subst e
      exact bootWals_ne_root hw hr hJ rfl
    · obtain ⟨⟨a, j⟩, hj, e⟩ := List.mem_map.1 h
      simp only at e; subst e
      exact bootSubs_ne_root hw hr hj
  · subst e
    obtain ⟨⟨a, J⟩, hJ, e⟩ := List.mem_map.1 hx
    simp only at e; subst e
    obtain ⟨⟨a', j⟩, hj, e⟩ := List.mem_map.1 hy
    simp only at e; subst e
    exact bootWals_not_sub hw hr hJ hj

theorem bootTaken_sub {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) : ∀ j ∈ bootTaken m jr, j ∈ (GMap.toList m).map (·.1) := by
  intro j hj
  apply mem_dom.2
  have hjr : jr ∈ m := hw.1 jr (Reach.root r jr hr)
  unfold bootTaken at hj
  rcases List.mem_cons.1 hj with e | hj
  · rw [e]; exact hjr
  rcases List.mem_append.1 hj with h | h
  · obtain ⟨⟨a, J⟩, hJ, e⟩ := List.mem_map.1 h
    simp only at e; subst e
    exact bootWals_mem hw hJ
  · obtain ⟨⟨a, j'⟩, hj', e⟩ := List.mem_map.1 h
    simp only at e; subst e
    obtain ⟨-, -, -, -, hm⟩ := mem_bootSubs.1 hj'
    exact hm

/-- **The directories given back**: every other one of the tree. -/
def bootRest (m : Tree) (jr : Ino) : List Ino :=
  ((GMap.toList m).map (·.1)).filter (fun j => decide (j ∉ bootTaken m jr))

/-- The tree's directories: the taken ones and the others. -/
theorem dom_perm_taken {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) :
    ((GMap.toList m).map (·.1)).Perm (bootTaken m jr ++ bootRest m jr) := by
  have hd := dom_nodup m
  have hT := bootTaken_nodup hw hr
  refine (List.perm_ext_iff_of_nodup hd (List.nodup_append.2 ⟨hT, hd.filter _, fun x hx y hy e => ?_⟩)).2
    (fun j => ?_)
  · subst e
    exact of_decide_eq_true (List.mem_filter.1 hy).2 hx
  · rw [List.mem_append]
    constructor
    · intro h
      by_cases ht : j ∈ bootTaken m jr
      · exact .inl ht
      · exact .inr (List.mem_filter.2 ⟨h, decide_eq_true ht⟩)
    · rintro (h | h)
      · exact bootTaken_sub hw hr j h
      · exact (List.mem_filter.1 h).1

/-- **Another root's directory is given back.** -/
theorem mem_bootRest_root {R : List (GoString × Ino)} {m : Tree} (hw : TreeWf R m) {r r' : GoString}
    {jr j : Ino} (hr : (r, jr) ∈ R) (hr' : (r', j) ∈ R) (hne : j ≠ jr) : j ∈ bootRest m jr := by
  refine List.mem_filter.2 ⟨mem_dom.2 (hw.1 _ (.root r' j hr')), decide_eq_true (fun ht => ?_)⟩
  unfold bootTaken at ht
  rcases List.mem_cons.1 ht with rfl | ht
  · exact hne rfl
  rcases List.mem_append.1 ht with h | h
  · obtain ⟨⟨a, J⟩, hJ, e⟩ := List.mem_map.1 h
    simp only at e; subst e
    exact hw.2.2.2.1 _ _ _ (mem_bootWals.1 hJ).2 r' hr'
  · obtain ⟨⟨a, j'⟩, hj', e⟩ := List.mem_map.1 h
    simp only at e; subst e
    obtain ⟨-, J, he, hd, -⟩ := mem_bootSubs.1 hj'
    have e := tDesc_root hw hr' hd
    subst e
    exact hw.2.2.2.1 _ _ _ he r' hr'

/-! ## The files-only premise -/

/-- **Every WAL directory of the area holds only files** (the crash boot's premise: the ledger's `hfo`,
2026-11-14; its `nm.tmp` parts gone 2026-11-22, `Create` coping with any leftover `nm.tmp`: ledger
2026-11-22). -/
def BootFo (m : Tree) (jr : Ino) : Prop :=
  ∀ nm J, walNameOk nm → m.entry jr nm = some (.dir J) → FilesOnly (entsOf m J)

/-- **What of `BootFo` the crash's `NoDirX` does not give** (`walInv_crash` gives every WAL directory's
names but the pipeline's, `NoDirX`, and this): the pipeline names of every WAL directory hold no
directory (from the pipeline claims' halves in the invariant). -/
def BootFoRest (m : Tree) (jr : Ino) : Prop :=
  ∀ nm J, walNameOk nm → m.entry jr nm = some (.dir J) → ∀ b ∈ walTmps, ∀ J', entsOf m J !! b ≠ some (.dir J')

/-- **`BootFo` from the crash's `NoDirX` and the rest.** -/
theorem bootFo_of {m : Tree} {jr : Ino}
    (hx : ∀ nm J, walNameOk nm → m.entry jr nm = some (.dir J) → NoDirX (entsOf m J))
    (hr : BootFoRest m jr) : BootFo m jr := by
  intro nm J hw he c n hc
  cases n with
  | file i => exact ⟨i, rfl⟩
  | dir J' =>
    by_cases hct : c ∈ walTmps
    · exact absurd hc (hr nm J hw he c hct J')
    · exact absurd hc (hx nm J hw he c J' hct)

/-! ## The area's claims tagged with their name (`walAreaRes`'s) -/

/-- The whole claims of the directories under each `nm.<sfx>`, tagged with it. -/
def bootCls (V : Hist) (jr : Ino) : List (GoString × Claim) :=
  (bootSubs V.now jr).map (fun aj => (aj.1, (aj.2, NameSet.except [], namesOf V aj.2 (.except []))))

theorem restrictN_except_nil (e : Ents) : restrictN (.except []) e = e := by
  apply GMap.ext; intro b
  exact restrictN_lookup _ _ _ (by simp [NameSet.Mem])

theorem mem_clOf_bootCls {V : Hist} {jr : Ino} {b : GoString} {c : Claim} :
    c ∈ clOf (bootCls V jr) b ↔ (b, c.1) ∈ bootSubs V.now jr ∧
      c = (c.1, NameSet.except [], namesOf V c.1 (.except [])) := by
  unfold clOf bootCls
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨b', c'⟩, hm, rfl⟩
    obtain ⟨hm2, hb⟩ := List.mem_filter.1 hm
    have hb := of_decide_eq_true hb
    simp only at hb; subst hb
    obtain ⟨⟨a, j⟩, hj, e⟩ := List.mem_map.1 hm2
    cases e
    exact ⟨hj, rfl⟩
  · rintro ⟨hj, e⟩
    refine ⟨(b, c), List.mem_filter.2 ⟨List.mem_map.2 ⟨(b, c.1), hj, ?_⟩, decide_eq_true rfl⟩, rfl⟩
    rw [e]

/-- **`walAreaRes`'s `SubCover`**: the tagged claims cover every directory under an `nm.<sfx>`. -/
theorem bootCls_subCover {R : List (GoString × Ino)} {V : Hist} (hw : TreeWf R V.now) {r : GoString}
    {jr : Ino} (hr : (r, jr) ∈ R) (b : GoString) (hb : (bootN V.now jr).Mem b)
    (hnw : ¬ walNameOk b) :
    SubCover (clOf (bootCls V jr) b) ((namesOf V jr (bootN V.now jr)).cur !! b) := by
  intro J hJ J' hreach
  have he : V.now.entry jr b = some (.dir J) := by
    have : (namesOf V jr (bootN V.now jr)).cur !! b = V.now.entry jr b := by
      show restrictN _ (entsOf V.now jr) !! b = _
      rw [restrictN_lookup _ _ _ hb, entsOf_lookup]
    rw [← this]; exact hJ
  have hs := bootN_subSlot hb hnw he
  have hJm : J ∈ V.now := (hw.2.2.1 _ _ _ he).2 J (List.mem_singleton_self _)
  -- every directory reached through the tagged claims is under `J`
  have hd : ∀ K K', ClReach (clOf (bootCls V jr) b) K K' → TDesc V.now J K → TDesc V.now J K' := by
    intro K K' h
    induction h with
    | refl => exact id
    | step K1 K2 K3 h c hc hcur _ ih =>
      intro hK1
      apply ih
      obtain ⟨-, e⟩ := mem_clOf_bootCls.1 hc
      simp only [Prod.mk.injEq, true_and] at e
      rw [e] at hcur
      have : V.now.entry K1 c = some (.dir K2) := by
        show _ = _
        have h1 : (namesOf V K1 (.except [])).cur !! c = V.now.entry K1 c := by
          show restrictN _ (entsOf V.now K1) !! c = _
          rw [restrictN_except_nil, entsOf_lookup]
        rw [← h1]; exact hcur
      exact .step K1 c K2 hK1 this
  have hJ' := hd J J' hreach .refl
  refine ⟨namesOf V J' (.except []), mem_clOf_bootCls.2 ⟨?_, rfl⟩⟩
  exact mem_bootSubs.2 ⟨hs, J, he, hJ', tDesc_mem hw hJm hJ'⟩

/-- **`walAreaRes`'s ranks**: the claims under a name, read off a well-formed tree, hold no cycle. -/
theorem bootCls_ranked {R : List (GoString × Ino)} {V : Hist} (hw : TreeWf R V.now) (jr : Ino)
    (b : GoString) : ClRanked (clOf (bootCls V jr) b) :=
  ClRanked.of_tree hw (fun c hc x n hx => by
    obtain ⟨-, e⟩ := mem_clOf_bootCls.1 hc
    rw [show c.2.2 = namesOf V c.1 (.except []) from congrArg (·.2.2) e] at hx
    have e2 : (namesOf V c.1 (.except [])).cur = entsOf V.now c.1 := by
      show restrictN _ (entsOf V.now c.1) = _
      exact restrictN_except_nil _
    rw [e2, entsOf_lookup] at hx
    exact hx)

end pure

end WalFs
end EtcdGrove
end Perennial

end
