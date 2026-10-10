/-
The pure model of bbolt's page-id lists (`common.Pgids`): page ids are `uint64`s, ordered
unsigned (`Pgids.Less`, and `Mergepgids`'s `lead[i] > follow[0]`).
-/
module

public import Perennial.Proof.ProofPrelude

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- Sorted, unsigned (duplicates allowed: `Mergepgids` does not need them distinct). -/
def PgidsSorted (l : List w64) : Prop :=
  l.Pairwise (fun x y => uint.Z x ≤ uint.Z y)

theorem PgidsSorted.take_drop {ls : List w64} (h : PgidsSorted ls) (n : Nat) :
    PgidsSorted (ls.take n) ∧ PgidsSorted (ls.drop n) ∧
      ∀ x ∈ ls.take n, ∀ y ∈ ls.drop n, uint.Z x ≤ uint.Z y := by
  have h' := h
  rw [PgidsSorted, ← List.take_append_drop n ls, List.pairwise_append] at h'
  exact h'

/-- The head of a sorted list is below all of it. -/
theorem PgidsSorted.head_le {f0 : w64} {fs : List w64} (h : PgidsSorted (f0 :: fs)) :
    ∀ y ∈ f0 :: fs, uint.Z f0 ≤ uint.Z y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact Int.le_refl _
  · exact (List.pairwise_cons.mp h).1 y hy

/-- One step of `Mergepgids`' loop: `merged` takes the prefix of `lead` (`ls`) below
`follow[0]`; it stays sorted and below what is left (`follow` and the rest of `lead`). -/
theorem merge_step {ms ls fs : List w64} {f0 : w64} (n : Nat)
    (Hms : PgidsSorted ms) (Hls : PgidsSorted ls) (Hfs : PgidsSorted fs)
    (Hle : ∀ x ∈ ms, ∀ y ∈ ls ++ fs, uint.Z x ≤ uint.Z y)
    (Hf0 : fs.head? = some f0)
    (Hbelow : ∀ x ∈ ls.take n, uint.Z x ≤ uint.Z f0) :
    PgidsSorted (ms ++ ls.take n) ∧
      ∀ x ∈ ms ++ ls.take n, ∀ y ∈ fs ++ ls.drop n, uint.Z x ≤ uint.Z y := by
  obtain ⟨Ht, -, Htd⟩ := Hls.take_drop n
  obtain ⟨fs', rfl⟩ : ∃ fs', fs = f0 :: fs' := by
    cases fs with
    | nil => simp at Hf0
    | cons a fs' => simp only [List.head?_cons, Option.some.injEq] at Hf0; exact ⟨fs', by rw [Hf0]⟩
  have Hhead := Hfs.head_le
  constructor
  · rw [PgidsSorted, List.pairwise_append]
    refine ⟨Hms, Ht, fun x hx y hy => Hle x hx y ?_⟩
    exact List.mem_append_left _ (List.mem_of_mem_take hy)
  · intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hy with hy | hy
      · exact Hle x hx y (List.mem_append_right _ hy)
      · exact Hle x hx y (List.mem_append_left _ (List.mem_of_mem_drop hy))
    · rcases List.mem_append.mp hy with hy | hy
      · exact Int.le_trans (Hbelow x hx) (Hhead y hy)
      · exact Htd x hx y hy

/-- The end of `Mergepgids`' loop: all of `lead` was below `follow[0]`. -/
theorem merge_done {ms ls fs : List w64} {f0 : w64}
    (Hms : PgidsSorted ms) (Hls : PgidsSorted ls) (Hfs : PgidsSorted fs)
    (Hle : ∀ x ∈ ms, ∀ y ∈ ls ++ fs, uint.Z x ≤ uint.Z y)
    (Hf0 : fs.head? = some f0)
    (Hbelow : ∀ x ∈ ls, uint.Z x ≤ uint.Z f0) :
    PgidsSorted (ms ++ ls ++ fs) := by
  have := merge_step ls.length Hms Hls Hfs Hle Hf0 (by rw [List.take_length]; exact Hbelow)
  rw [List.take_length, List.drop_length, List.append_nil] at this
  rw [PgidsSorted, List.pairwise_append]
  exact ⟨this.1, Hfs, this.2⟩

end bbolt
end EtcdGrove
end Perennial
