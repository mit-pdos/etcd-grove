/-
The epoch summaries' ids (`summaryId p`, `"Epoch"` and the order's replicas): ASCII, a read
command (not a put), distinct from `"nil"` and from the client's request ids (package `laws`).
-/
module

public import Dsverify.Proof.raxos.Smr.OpId

@[expose] public section

noncomputable section

namespace Perennial.raxos.sumid

open Perennial Perennial.raxos Perennial.raxos.pure

theorem mem_flatten_intersperse {α} (sep : List α) (l : List (List α)) (b : α)
    (h : b ∈ (List.intersperse sep l).flatten) : b ∈ sep ∨ ∃ s ∈ l, b ∈ s := by
  induction l with
  | nil => simp at h
  | cons s l ih =>
    cases l with
    | nil => simp at h; exact Or.inr ⟨s, by simp, h⟩
    | cons s' l' =>
      simp only [List.intersperse_cons_cons, List.flatten_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact Or.inr ⟨s, by simp, h⟩
      · exact Or.inl h
      · rcases ih (by simpa using h) with h' | ⟨t, ht, hb⟩
        · exact Or.inl h'
        · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, hb⟩

theorem summaryId_take1 (p : List Nat) : (summaryId p).take 1 = go!"E" := by
  simp [summaryId]

theorem summaryId_ne_nil (p : List Nat) : summaryId p ≠ go!"nil" := by
  intro h
  have := congrArg (List.take 1) h
  rw [summaryId_take1] at this
  simp at this

theorem summaryId_ne_opId (p : List Nat) (c j : Nat) : summaryId p ≠ opId c j :=
  fun h => opid.opId_ne_summary c j p h.symm

theorem summaryId_cmdPut (p : List Nat) : cmdPut (summaryId p) = none := by
  simp [cmdPut, summaryId_take1]

theorem summaryId_ascii (p : List Nat) : msg.asciiOk (summaryId p) := by
  intro b hb
  simp only [summaryId, List.mem_append] at hb
  rcases hb with hb | hb
  · revert b; decide
  · rcases mem_flatten_intersperse _ _ b hb with hb | ⟨s, hs, hb⟩
    · simp at hb; subst hb; decide
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hs
      have := opid.bstr_digits k b hb; omega

end Perennial.raxos.sumid
