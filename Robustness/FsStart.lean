/-
Lean-first (no Rocq counterpart).

# The Linux file extension's initial state is satisfiable

`FsInit` (`GooseLang/Ext/Fs/Impl.lean`) is the file extension's `initLocal`, an antecedent of every
`Robust` statement on a machine with files. `fsOneRoot r` is a state with one root `r`, an empty
directory, and nothing else; `fsInit_fsOneRoot` proves it initial. Perennial asks each extension's
initial states to be satisfiable (`ExtSemantics.initLocal`'s docstring, `Lang.lean`); this is that
witness for the file extension, which the top-level statements' witnesses
(`Robustness/PremiseSat.lean`) build on. Untrusted: nothing uses it but the witnesses.

Also: lookups in such a state (`lookup_root_or_none`: with every directory empty, a path names
something only if it is a root; `fsOneRoot_lookup_append`, `fsOneRoot_lookup_joinPath`: nothing is
below the root), and the multi-root state `fsRoots rs` (one empty root per path of `rs`,
`fsInit_fsRoots`), for statements whose start state has several roots.
-/
module

public import Robustness.PremiseSat
public import GooseLang.Ext.Fs.Impl
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

open Fs

/-- The file extension's state with one root, the path `r`, an empty directory of inode `0`, and no
file. -/
def fsOneRoot (r : GoString) : OsState :=
  { fs := { roots := [(r, 0)], treeDur := <[0 := (∅ : Dir)]> ∅, metaLog := [],
            committed := fun _ => False, files := ∅, nextIno := 1, stamp := 0 }
    proc := ProcState.empty }

/-- The root's directory has no entry, and no other directory exists. -/
theorem fsOneRoot_entry (r : GoString) (j : Ino) (b : GoString) :
    (fsOneRoot r).fs.treeDur.entry j b = none := by
  by_cases h : j = 0
  · subst h; simp [fsOneRoot, Tree.entry]
  · have h' : (0 : Nat) ≠ j := fun e => h e.symm
    simp [fsOneRoot, Tree.entry, h']

theorem fsOneRoot_mem (r : GoString) (j : Ino) : j ∈ (fsOneRoot r).fs.treeDur ↔ j = 0 := by
  rw [GMap.mem_iff]
  by_cases h : j = 0
  · subst h; simp [fsOneRoot]
  · have h' : (0 : Nat) ≠ j := fun e => h e.symm
    simp [fsOneRoot, h, h']

theorem fsOneRoot_reach (r : GoString) {j : Ino}
    (h : Reach (fsOneRoot r).fs.roots (fsOneRoot r).fs.treeDur j) : j = 0 := by
  cases h with
  | root r' j hj => exact (by simpa [fsOneRoot] using hj : r' = r ∧ j = 0).2
  | child j0 b j' _ he => simp [fsOneRoot_entry] at he

/-- **`fsOneRoot r` is an initial state** (`FsInit`) when `r` is a root's form: canonical and
absolute. -/
theorem fsInit_fsOneRoot (r : GoString) (hr : RootForm r) : FsInit (fsOneRoot r) := by
  refine ⟨rfl, rfl, fun _ h => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [fsOneRoot], by simp [fsOneRoot], ?_⟩
    intro x hx
    simp only [fsOneRoot, List.mem_singleton] at hx
    subst hx
    refine ⟨hr, fun r' hr' hne => ?_⟩
    simp only [fsOneRoot, List.mem_singleton] at hr'
    subst hr'
    exact absurd rfl hne
  · refine ⟨fun j hj => (fsOneRoot_mem r j).2 (fsOneRoot_reach r hj), fun j hj => ?_,
      fun j b n he => by simp [fsOneRoot_entry] at he, fun j b j' he => by simp [fsOneRoot_entry] at he,
      fun j1 b1 j2 b2 n he => by simp [fsOneRoot_entry] at he⟩
    left
    rw [(fsOneRoot_mem r j).1 hj]
    exact Reach.root r 0 (by simp [fsOneRoot])
  · rintro i ⟨j, b, he⟩; simp [fsOneRoot_entry] at he
  · intro i f hf; simp [fsOneRoot] at hf
  · intro i hi; simp [fsOneRoot, GMap.mem_iff] at hi
  · intro j hj; rw [(fsOneRoot_mem r j).1 hj]; simp [fsOneRoot]

/-- A one-component absolute path `/c` is a root's form when `c` is a valid name. -/
theorem rootForm_one (c : GoString) (hc : NameOk c) : RootForm (slashB :: c) :=
  ⟨[c], by simp, by simpa using hc, by simp [joinPath]⟩

/-! ## Lookups in a state whose directories are all empty -/

/-- In a state whose directories have no entry below a root, a path names something only if it is
a root, and then it names the root's directory. -/
theorem lookup_root_or_none (st : OsState) (hw : ∀ j c cs, walk st.tree (.dir j) (c :: cs) = none)
    (p : GoString) :
    st.lookup p = none ∨ ∃ rj ∈ st.fs.roots, p = rj.1 ∧ st.lookup p = some (.dir rj.2) := by
  by_cases h : ∃ (rj : GoString × Ino) (cs : List GoString), rj ∈ st.fs.roots ∧
      (∀ c ∈ cs, NameOk c) ∧ p = joinPath rj.1 cs
  · have hl : st.lookup p = walk st.tree (.dir h.choose.2) h.choose_spec.choose := by
      unfold OsState.lookup; rw [dite_cond_eq_true (eq_true h)]
    have hspec := h.choose_spec.choose_spec
    revert hl hspec
    generalize h.choose_spec.choose = cs
    generalize h.choose = rj
    intro hl hspec
    cases cs with
    | nil =>
      right
      refine ⟨rj, hspec.1, by simpa [joinPath] using hspec.2.2, ?_⟩
      rw [hl]; simp [walk]
    | cons c cs => left; rw [hl]; exact hw _ _ _
  · left; unfold OsState.lookup; rw [dite_cond_eq_false (eq_false h)]

theorem fsOneRoot_tree (r : GoString) : (fsOneRoot r).tree = (fsOneRoot r).fs.treeDur := rfl

theorem fsOneRoot_walk (r : GoString) (j : Ino) (c : GoString) (cs : List GoString) :
    walk (fsOneRoot r).tree (.dir j) (c :: cs) = none := by
  rw [fsOneRoot_tree]; simp [walk, fsOneRoot_entry]

/-- **Nothing is below the root of `fsOneRoot r`.** -/
theorem fsOneRoot_lookup_append (r x : GoString) (hx : x ≠ []) : (fsOneRoot r).lookup (r ++ x) = none := by
  rcases lookup_root_or_none _ (fsOneRoot_walk r) (r ++ x) with h | ⟨rj, hm, hp, -⟩
  · exact h
  · have hm' : rj = (r, 0) := by simpa [fsOneRoot] using hm
    subst hm'
    have h1 : (r ++ x).length = r.length := congrArg List.length hp
    rw [List.length_append] at h1
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hx

theorem fsOneRoot_lookup_joinPath (r : GoString) (cs : List GoString) (hcs : cs ≠ []) :
    (fsOneRoot r).lookup (joinPath r cs) = none := by
  unfold joinPath
  apply fsOneRoot_lookup_append
  cases cs with
  | nil => exact absurd rfl hcs
  | cons c cs => simp [List.flatMap_cons]

theorem fsOneRoot_root_mem (r : GoString) : r ∈ (fsOneRoot r).fs.roots.map (·.1) := by
  simp [fsOneRoot]

/-! ## Several roots

`fsRoots rs`: one root per path of `rs`, the `k`-th an empty directory of inode `k`, and nothing else
(the multi-root `fsOneRoot`, for the statements whose start state has several roots: the WAL tester's
area and oracle directory, the etcd examples' WAL areas and data directories). -/

/-- The directories `0 … n - 1`, each empty. -/
def emptyDirs (n : Nat) : Tree :=
  ⟨fun j => if j < n then some ∅ else none,
   ⟨List.range n, fun j h => List.mem_range.2 (by
      by_cases hj : j < n
      · exact hj
      · simp [hj] at h)⟩⟩

theorem emptyDirs_lookup (n j : Nat) : emptyDirs n !! j = if j < n then some ∅ else none := rfl

/-- The paths `rs` numbered from `k` (inode numbers, `Ino`, stated as `Nat` for `omega`). -/
def rootsFrom : List GoString → Nat → List (GoString × Nat)
  | [], _ => []
  | r :: rs, k => (r, k) :: rootsFrom rs (k + 1)

theorem rootsFrom_fst (rs : List GoString) (k : Nat) : (rootsFrom rs k).map (·.1) = rs := by
  induction rs generalizing k with
  | nil => rfl
  | cons r rs ih => simp [rootsFrom, ih]

theorem rootsFrom_mem_fst {rs : List GoString} {k : Nat} {x : GoString × Nat}
    (h : x ∈ rootsFrom rs k) : x.1 ∈ rs := by
  have h' : x.1 ∈ (rootsFrom rs k).map (·.1) := List.mem_map.2 ⟨x, h, rfl⟩
  rwa [rootsFrom_fst] at h'

theorem rootsFrom_snd {rs : List GoString} {k : Nat} {x : GoString × Nat}
    (h : x ∈ rootsFrom rs k) : k ≤ x.2 ∧ x.2 < k + rs.length := by
  induction rs generalizing k with
  | nil => simp [rootsFrom] at h
  | cons r rs ih =>
    simp only [rootsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · show k ≤ k ∧ k < k + (rs.length + 1); exact ⟨Nat.le_refl _, by omega⟩
    · obtain ⟨h1, h2⟩ := ih h
      simp only [List.length_cons]; exact ⟨by omega, by omega⟩

theorem rootsFrom_snd_nodup (rs : List GoString) (k : Nat) : ((rootsFrom rs k).map (·.2)).Nodup := by
  induction rs generalizing k with
  | nil => simp [rootsFrom]
  | cons r rs ih =>
    simp only [rootsFrom, List.map_cons, List.nodup_cons]
    refine ⟨fun hk => ?_, ih (k + 1)⟩
    obtain ⟨x, hm, hj⟩ := List.mem_map.1 hk
    have h1 : k + 1 ≤ x.2 := (rootsFrom_snd hm).1
    have h2 : x.2 = k := hj
    omega

theorem rootsFrom_mem_get (rs : List GoString) (k j : Nat) (hj : j < rs.length) :
    (rs[j], k + j) ∈ rootsFrom rs k := by
  induction rs generalizing k j with
  | nil => simp at hj
  | cons r rs ih =>
    cases j with
    | zero => simp [rootsFrom]
    | succ j =>
      have := ih (k + 1) j (by simpa using hj)
      simp only [rootsFrom, List.mem_cons, List.getElem_cons_succ]
      right; rwa [show k + (j + 1) = k + 1 + j by omega]

/-- Each path of `rs` is a root. -/
theorem rootsFrom_mem_of {rs : List GoString} {r : GoString} (h : r ∈ rs) (k : Nat) :
    ∃ j, (r, j) ∈ rootsFrom rs k := by
  rw [← rootsFrom_fst rs k] at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact ⟨x.2, hx⟩

/-- The file extension's state with the roots `rs`, the `k`-th an empty directory of inode `k`, and
no file. -/
def fsRoots (rs : List GoString) : OsState :=
  { fs := { roots := rootsFrom rs 0, treeDur := emptyDirs rs.length, metaLog := [],
            committed := fun _ => False, files := ∅, nextIno := rs.length, stamp := 0 }
    proc := ProcState.empty }

/-- No directory of `fsRoots rs` has an entry. -/
theorem fsRoots_entry (rs : List GoString) (j : Ino) (b : GoString) :
    (fsRoots rs).fs.treeDur.entry j b = none := by
  simp only [fsRoots, Tree.entry, emptyDirs_lookup]
  split <;> simp

theorem fsRoots_mem (rs : List GoString) (j : Ino) : j ∈ (fsRoots rs).fs.treeDur ↔ j < rs.length := by
  rw [GMap.mem_iff]
  by_cases h : j < rs.length <;> simp [fsRoots, emptyDirs_lookup, h]

theorem fsRoots_reach (rs : List GoString) {j : Ino}
    (h : Reach (fsRoots rs).fs.roots (fsRoots rs).fs.treeDur j) : j < rs.length := by
  cases h with
  | root r' j hj => simpa using (rootsFrom_snd (k := 0) hj).2
  | child j0 b j' _ he => simp [fsRoots_entry] at he

theorem fsRoots_root (rs : List GoString) {r : GoString} (h : r ∈ rs) :
    ∃ j, (r, j) ∈ (fsRoots rs).fs.roots := rootsFrom_mem_of h 0

/-- **`fsRoots rs` is an initial state** (`FsInit`) when the paths of `rs` are distinct roots' forms,
none in another's tree. -/
theorem fsInit_fsRoots (rs : List GoString) (hnd : rs.Nodup) (hf : ∀ r ∈ rs, RootForm r)
    (hu : ∀ r ∈ rs, ∀ r' ∈ rs, r ≠ r' → ¬ IsUnder r r') : FsInit (fsRoots rs) := by
  refine ⟨rfl, rfl, fun _ h => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp only [fsRoots, rootsFrom_fst]; exact hnd, rootsFrom_snd_nodup _ _, ?_⟩
    intro x hx
    have hx1 : x.1 ∈ rs := rootsFrom_mem_fst hx
    exact ⟨hf _ hx1, fun r' hr' hne => hu _ hx1 _ (rootsFrom_mem_fst hr') hne⟩
  · refine ⟨fun j hj => (fsRoots_mem rs j).2 (fsRoots_reach rs hj), fun j hj => ?_,
      fun j b n he => by simp [fsRoots_entry] at he, fun j b j' he => by simp [fsRoots_entry] at he,
      fun j1 b1 j2 b2 n he => by simp [fsRoots_entry] at he⟩
    left
    have hj' := (fsRoots_mem rs j).1 hj
    have hm := rootsFrom_mem_get rs 0 j hj'
    rw [Nat.zero_add] at hm
    exact Reach.root _ j hm
  · rintro i ⟨j, b, he⟩; simp [fsRoots_entry] at he
  · intro i f hf; simp [fsRoots] at hf
  · intro i hi; simp [fsRoots, GMap.mem_iff] at hi
  · intro j hj; exact (fsRoots_mem rs j).1 hj

theorem fsRoots_tree (rs : List GoString) : (fsRoots rs).tree = (fsRoots rs).fs.treeDur := rfl

theorem fsRoots_walk (rs : List GoString) (j : Ino) (c : GoString) (cs : List GoString) :
    walk (fsRoots rs).tree (.dir j) (c :: cs) = none := by
  rw [fsRoots_tree]; simp [walk, fsRoots_entry]

/-- **Nothing is below a root of `fsRoots rs`** but another root: a path that is no root names
nothing. -/
theorem fsRoots_lookup_none (rs : List GoString) (p : GoString) (hp : p ∉ rs) :
    (fsRoots rs).lookup p = none := by
  rcases lookup_root_or_none _ (fsRoots_walk rs) p with h | ⟨rj, hm, hpr, -⟩
  · exact h
  · exact absurd (hpr ▸ rootsFrom_mem_fst hm) hp

end Robustness
end Perennial

end
