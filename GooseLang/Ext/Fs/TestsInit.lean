/- The start hypotheses of the examples' crash theorems are satisfiable: an empty root `/r` is
`FsInit`, `/r` is a root, and `/r/db` names nothing (`fsInit0`, `root0`, `db_none`), so
`BootCrashSafety`, crashlog's and walfs's results are not vacuous for want of a start state. From
the final review (`notes/axiom-review/fs-final.md`). Untrusted (a check of the trusted
definitions). -/
module

public import GooseLang.Ext.Fs.TreeLemmas
public import GooseLang.Ext.Fs.Tests

@[expose] public section

namespace Perennial
namespace Fs
namespace TestsInit

open Perennial.Fs.Tests
def tree0 : Tree := {[1 := ∅]}

def st0 : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := tree0, metaLog := [], committed := fun _ => False,
            files := ∅, nextIno := 2, stamp := 0 },
    proc := ProcState.empty }

def rB : GoString := go!"r"
def dbB' : GoString := go!"db"

theorem rootP_eq : rootP = joinPath [] [rB] := by decide

theorem nameOk_r : NameOk rB := by decide
theorem nameOk_db : NameOk dbB' := by decide

theorem entry0 (j : Ino) (b : GoString) : tree0.entry j b = none := by
  unfold Tree.entry tree0
  by_cases h : j = 1
  · subst h; simp
  · simp [h]

theorem mem_tree0 (j : Ino) : j ∈ tree0 ↔ j = 1 := by
  rw [GMap.mem_iff]; unfold tree0; rw [GMap.lookup_singleton_iff]
  by_cases h : j = 1
  · subst h; simp
  · rw [if_neg (Ne.symm h)]; simp [h]

theorem roots0 : RootsOk st0.fs.roots := by
  refine ⟨by simp [st0], by simp [st0], fun r hr => ?_⟩
  simp only [st0, List.mem_singleton] at hr
  subst hr
  refine ⟨⟨[rB], by simp, by simpa using nameOk_r, rootP_eq⟩, fun r' hr' hne => ?_⟩
  simp only [st0, List.mem_singleton] at hr'
  subst hr'; exact absurd rfl hne

theorem fsInit0 : FsInit st0 := by
  refine ⟨rfl, rfl, fun _ h => h, roots0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j hj
    cases hj with
    | root r j h =>
      simp only [st0, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact (mem_tree0 1).2 rfl
    | child j b j' _ he => simp [st0, entry0] at he
  · intro j hj
    left
    have := (mem_tree0 j).1 hj
    subst this
    exact .root rootP 1 (by simp [st0])
  · intro j b n he; simp [st0, entry0] at he
  · intro j b j' he; simp [st0, entry0] at he
  · intro j1 b1 j2 b2 n he; simp [st0, entry0] at he
  · intro i ⟨j, b, he⟩; simp [st0, entry0] at he
  · intro i f hf; simp [st0] at hf
  · intro i hi; rw [GMap.mem_iff] at hi; simp [st0] at hi
  · intro j hj
    have := (mem_tree0 j).1 hj
    subst this; decide

theorem root0 : ∃ j, (rootP, j) ∈ st0.fs.roots := ⟨1, by simp [st0]⟩

theorem db_none : st0.lookup (rootP ++ go!"/db") = none := by
  have h : rootP ++ go!"/db" = joinPath rootP [dbB'] := by decide
  rw [h, lookup_joinPath (j := 1) roots0 (by simp [st0]) (by simpa using nameOk_db)]
  simp [walk, OsState.tree, st0, replay, entry0]



end TestsInit
end Fs
end Perennial

end
