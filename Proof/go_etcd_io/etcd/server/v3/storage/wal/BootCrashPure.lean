/- Lean-first (no Rocq counterpart).

# The crash boot's files, pure (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log")

The crash boot hands the program and the new invariant whole files of the crashed tree that are no
segment: a WAL directory's entries at its non-`.wal` names (the invariant's `walOthers`, its
pipeline names' `walTmpsRes`), and a WAL name's temporary directory's probe `.touch` (`walAreaRes`'s
`tmpClTouch`). `bootFiles m jr` lists their inodes, the area being `jr` in the tree `m`: distinct, by
the tree's unique naming (`TreeWf`'s last part), and none a segment's (`.wal` names).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **The name `b` of a directory at the area's name `a`, taken at the crash boot**: a non-`.wal`
name of a WAL directory, or the probe `.touch` of a WAL name's temporary directory. -/
def BootTake (a b : GoString) : Prop :=
  (walNameOk a ∧ walNameP b = false) ∨ ((∃ nm, walNameOk nm ∧ a = tmpName nm) ∧ b = go!".touch")

open Classical in
/-- The files the crash boot takes from the directory `J` at the area's name `a`. -/
def dirBootFiles (m : Tree) (a : GoString) (J : Ino) : List Ino :=
  (GMap.toList (entsOf m J)).filterMap (fun be => match be.2 with
    | .file i => if BootTake a be.1 then some i else none
    | .dir _ => none)

/-- **The files the crash boot takes**, the area being `jr` in the tree `m`. -/
def bootFiles (m : Tree) (jr : Ino) : List Ino :=
  (GMap.toList (entsOf m jr)).flatMap (fun an => match an.2 with
    | .dir J => dirBootFiles m an.1 J
    | .file _ => [])

theorem entsOf_lookup (m : Tree) (j : Ino) (b : GoString) : entsOf m j !! b = m.entry j b := by
  unfold entsOf Tree.entry
  cases m !! j <;> rfl

/-- Unique naming (`TreeWf`'s last part). -/
def UniqNames (m : Tree) : Prop :=
  ∀ j1 b1 j2 b2 n, m.entry j1 b1 = some n → m.entry j2 b2 = some n → j1 = j2 ∧ b1 = b2

theorem uniqNames_of_wf {R : List (GoString × Ino)} {m : Tree} (h : TreeWf R m) : UniqNames m :=
  h.2.2.2.2

theorem mem_dirBootFiles {m : Tree} {a : GoString} {J i : Ino} :
    i ∈ dirBootFiles m a J ↔ ∃ b, m.entry J b = some (.file i) ∧ BootTake a b := by
  unfold dirBootFiles
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨b, n⟩, hm, hf⟩
    have he := (GMap.mem_toList _ _ _).1 hm
    rw [entsOf_lookup] at he
    cases n with
    | file i' =>
      simp only at hf
      split at hf
      · next ht => cases hf; exact ⟨b, he, ht⟩
      · cases hf
    | dir _ => simp at hf
  · rintro ⟨b, he, ht⟩
    refine ⟨(b, .file i), (GMap.mem_toList _ _ _).2 (by rw [entsOf_lookup]; exact he), ?_⟩
    simp only
    rw [if_pos ht]

theorem mem_bootFiles {m : Tree} {jr i : Ino} :
    i ∈ bootFiles m jr ↔ ∃ a J b, m.entry jr a = some (.dir J) ∧ m.entry J b = some (.file i) ∧
      BootTake a b := by
  unfold bootFiles
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨a, n⟩, hm, hi⟩
    have he := (GMap.mem_toList _ _ _).1 hm
    rw [entsOf_lookup] at he
    cases n with
    | dir J =>
      obtain ⟨b, hb, ht⟩ := mem_dirBootFiles.1 hi
      exact ⟨a, J, b, he, hb, ht⟩
    | file _ => cases hi
  · rintro ⟨a, J, b, he, hb, ht⟩
    exact ⟨(a, .dir J), (GMap.mem_toList _ _ _).2 (by rw [entsOf_lookup]; exact he),
      mem_dirBootFiles.2 ⟨b, hb, ht⟩⟩

theorem toList_nodup {V : Type} (M : GMap GoString V) : (GMap.toList M).Nodup :=
  List.Pairwise.of_map Prod.fst (fun a b h e => h (by rw [e])) (GMap.toList_keys_nodup M)

/-- A list's `flatMap` has no duplicate if each part has none and no two parts meet. -/
theorem nodup_flatMap_of {α β : Type} {f : α → List β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, (f x).Nodup) →
      (∀ x ∈ l, ∀ y ∈ l, ∀ z, z ∈ f x → z ∈ f y → x = y) → (l.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | x :: l, hn, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    have hx : x ∉ l := (List.nodup_cons.1 hn).1
    refine ⟨h1 x (List.mem_cons_self ..),
      nodup_flatMap_of (List.nodup_cons.1 hn).2 (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
        (fun y hy y' hy' => h2 y (List.mem_cons_of_mem _ hy) y' (List.mem_cons_of_mem _ hy')), ?_⟩
    intro z hz z' hz' e
    subst e
    obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.1 hz'
    have := h2 x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy) z hz hzy
    subst this
    exact hx hy

/-- A list's `filterMap` has no duplicate if no two of its elements map to the same value. -/
theorem nodup_filterMap_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') →
      (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hn, h => by
    have ha : a ∉ l := (List.nodup_cons.1 hn).1
    have ih := nodup_filterMap_of (List.nodup_cons.1 hn).2
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    rw [List.filterMap_cons]
    cases hf : f a with
    | none => exact ih
    | some b =>
      refine List.nodup_cons.2 ⟨fun hb => ?_, ih⟩
      obtain ⟨a', ha', hf'⟩ := List.mem_filterMap.1 hb
      have := h a (List.mem_cons_self ..) a' (List.mem_cons_of_mem _ ha') b hf hf'
      subst this
      exact ha ha'

open Classical in
/-- An element of `dirBootFiles`'s list maps to `i` only from a file entry `i`. -/
theorem dirBootFiles_some {a : GoString} {be : GoString × Node} {i : Ino}
    (h : (match be.2 with
      | .file i => if BootTake a be.1 then some i else none
      | .dir _ => none : Option Ino) = some i) : be.2 = .file i := by
  obtain ⟨b, n⟩ := be
  cases n with
  | file i' =>
    simp only at h ⊢
    split at h
    · cases h; rfl
    · cases h
  | dir _ => simp at h

/-- **The crash boot's files are distinct**, by unique naming. -/
theorem bootFiles_nodup {m : Tree} (hu : UniqNames m) (jr : Ino) : (bootFiles m jr).Nodup := by
  unfold bootFiles
  refine nodup_flatMap_of (toList_nodup _) (fun an _ => ?_) (fun an han an' han' z hz hz' => ?_)
  · obtain ⟨a, n⟩ := an
    cases n with
    | file _ => exact List.nodup_nil
    | dir J =>
      unfold dirBootFiles
      refine nodup_filterMap_of (toList_nodup _) (fun be hbe be' hbe' i hi hi' => ?_)
      have e1 := dirBootFiles_some hi
      have e2 := dirBootFiles_some hi'
      have h1 := (GMap.mem_toList _ _ _).1 (show (be.1, be.2) ∈ _ from hbe)
      have h2 := (GMap.mem_toList _ _ _).1 (show (be'.1, be'.2) ∈ _ from hbe')
      rw [entsOf_lookup, e1] at h1
      rw [entsOf_lookup, e2] at h2
      have hb := (hu _ _ _ _ _ h1 h2).2
      obtain ⟨b, n⟩ := be
      obtain ⟨b', n'⟩ := be'
      simp only at e1 e2 hb
      subst hb e1 e2; rfl
  · obtain ⟨a, n⟩ := an
    obtain ⟨a', n'⟩ := an'
    have h1 := (GMap.mem_toList _ _ _).1 han
    have h2 := (GMap.mem_toList _ _ _).1 han'
    rw [entsOf_lookup] at h1 h2
    cases n with
    | file _ => cases hz
    | dir J =>
      cases n' with
      | file _ => cases hz'
      | dir J' =>
        obtain ⟨b, hb, -⟩ := mem_dirBootFiles.1 hz
        obtain ⟨b', hb', -⟩ := mem_dirBootFiles.1 hz'
        have hJ := (hu _ _ _ _ _ hb hb').1
        subst hJ
        have ha := (hu _ _ _ _ _ h1 h2).2
        subst ha; rfl

/-- A file the crash boot takes is at a non-`.wal` name or at `.touch`. -/
theorem bootTake_not_wal {a b : GoString} (h : BootTake a b) : walNameP b = false := by
  rcases h with ⟨-, h⟩ | ⟨-, rfl⟩
  · exact h
  · decide

end pure

end WalFs
end EtcdGrove
end Perennial

end
