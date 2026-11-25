/-
Lean-first (no Rocq counterpart).

# The Linux file extension's initial state is satisfiable

`FsInit` (`GooseLang/Ext/Fs/Impl.lean`) is the file extension's `initLocal`, an antecedent of every
`Robust` statement on a machine with files. `fsOneRoot r` is a state with one root `r`, an empty
directory, and nothing else; `fsInit_fsOneRoot` proves it initial. Perennial asks each extension's
initial states to be satisfiable (`ExtSemantics.initLocal`'s docstring, `Lang.lean`); this is that
witness for the file extension, which the top-level statements' witnesses
(`Robustness/PremiseSat.lean`) build on. Untrusted: nothing uses it but the witnesses.
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

end Robustness
end Perennial

end
