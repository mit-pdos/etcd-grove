/-
Facts about Lean's lists that belong to no Go package: the keys before the `i`-th of a list
(the order `wp_map_for_range` enumerates a map's keys in) and prefixes.

They are kept here until Lean's core library (or Perennial) has them: each is a candidate for an
independent proposal (CLAUDE.md, "Changes to Perennial"), and goes once its counterpart lands
(`notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- An element of a duplicate-free list is not among the elements before it. -/
theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {x : α}
    (hx : l[i]? = some x) : x ∉ l.take i := by
  intro hm
  have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  rw [hsplit] at h
  have hdrop : x ∈ l.drop i := by
    apply List.mem_of_getElem? (i := 0)
    rw [List.getElem?_drop]; simpa using hx
  exact (List.nodup_append.1 h).2.2 x hm x hdrop rfl

/-- The first `i + 1` elements: the first `i` and the `i`-th. -/
theorem mem_take_succ_iff {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) (x : α) :
    x ∈ l.take (i + 1) ↔ x ∈ l.take i ∨ x = a := by
  rw [List.take_add_one, h]
  simp

/-- A prefix with nothing past it is the whole list. -/
theorem prefix_drop_nil {α : Type} {sent recv : List α} (hp : recv <+: sent)
    (hd : sent.drop recv.length = []) : recv = sent := by
  obtain ⟨t, rfl⟩ := hp
  simp only [List.drop_left] at hd
  simp [hd]

end EtcdGrove
end Perennial
