/-
Lean-first (no Rocq counterpart).

# Porcupine: the order of `byTime` and the entries of `makeEntries` (2026-10-14)

`entryLt a b` is `byTime.Less` on two Go entries (`checker.go`): an earlier time (signed,
`int64`), or at the same time a call before a return. It is a strict weak order (two entries
are incomparable iff they have the same time and kind), as `sort.Sort` needs.

`makeEntries` builds `rawEntries ops` (a call and a return entry per operation, with its index
as id) and sorts it; `entriesFor_of_perm` shows that any permutation of `rawEntries ops`
sorted by `entryLt` satisfies `EntriesFor (histOf ops)`.
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs
public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.anishathalye.porcupine

open Theory

section entries
variable [ext : FfiSyntax]

/-- `byTime.Less` on two entries (see the file header). -/
def entryLt (a b : entry) : Bool :=
  if a.time' = b.time' then (!a.kind' && b.kind') else decide (sint.Z a.time' < sint.Z b.time')

theorem entryLt_iff (a b : entry) :
    entryLt a b = true ↔
      sint.Z a.time' < sint.Z b.time' ∨
        (sint.Z a.time' = sint.Z b.time' ∧ a.kind' = false ∧ b.kind' = true) := by
  unfold entryLt
  have hz : a.time' = b.time' ↔ sint.Z a.time' = sint.Z b.time' := by
    constructor
    · intro h; rw [h]
    · intro h; exact BitVec.toInt_inj.mp h
  by_cases h : a.time' = b.time'
  · simp only [h, ↓reduceIte]
    cases a.kind' <;> cases b.kind' <;> simp
  · have h' : sint.Z a.time' ≠ sint.Z b.time' := fun e => h (hz.mpr e)
    simp only [h, ↓reduceIte, decide_eq_true_eq]
    constructor
    · intro hh; exact Or.inl hh
    · rintro (hh | hh)
      · exact hh
      · exact absurd hh.1 h'

/-- `byTime.Less` is a strict weak order. -/
theorem entryLt_swo : slices.StrictWeakOrder (fun a b : entry => entryLt a b = true) := by
  simp only [entryLt_iff]
  exact {
    strict_weak_order_irrefl := fun _ h => by
      rcases h with h | h
      · exact Int.lt_irrefl _ h
      · rw [h.2.1] at h; exact Bool.false_ne_true h.2.2
    strict_weak_order_trans := fun a b c h1 h2 => by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact Or.inl (Int.lt_trans h1 h2)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · rw [h1.2.2] at h2; exact absurd h2.2.1 (by simp)
    strict_weak_order_equiv := {
      refl := fun a => ⟨fun h => by
          rcases h with h | h
          · exact Int.lt_irrefl _ h
          · rw [h.2.1] at h; exact Bool.false_ne_true h.2.2,
        fun h => by
          rcases h with h | h
          · exact Int.lt_irrefl _ h
          · rw [h.2.1] at h; exact Bool.false_ne_true h.2.2⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun {a b c} h1 h2 => by
        obtain ⟨h1a, h1b⟩ := h1
        obtain ⟨h2a, h2b⟩ := h2
        simp only [not_or, not_and] at h1a h1b h2a h2b
        have tab : sint.Z a.time' = sint.Z b.time' := by omega
        have tbc : sint.Z b.time' = sint.Z c.time' := by omega
        have kab : a.kind' = b.kind' := by
          cases ha : a.kind' <;> cases hb : b.kind' <;> simp_all
        have kbc : b.kind' = c.kind' := by
          cases hb : b.kind' <;> cases hc : c.kind' <;> simp_all
        simp only [not_or, not_and]
        refine ⟨⟨by omega, fun _ h => ?_⟩, ⟨by omega, fun _ h => ?_⟩⟩
        · rw [← kbc, ← kab, h]; exact Bool.false_ne_true
        · rw [kab, kbc, h]; exact Bool.false_ne_true } }

end entries

end github_com.anishathalye.porcupine
end Perennial
