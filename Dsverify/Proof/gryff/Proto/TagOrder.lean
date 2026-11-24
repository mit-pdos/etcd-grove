/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/TagOrder.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The tag order (`tagLt`, `tagLe`), `rmwTag`, and the frontier (`median3`): pure lemmas (U4).
-/
module

public import Dsverify.Proof.gryff.Proto.Model

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.proto

theorem tag_eq_iff (a b : PTag) : a = b ↔ a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2 := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b; simp

theorem tagLe_iff (a b : PTag) : tagLe a b ↔
    a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2))) := by
  unfold tagLe tagLt; rw [tag_eq_iff]; omega

theorem tagLt_irrefl (a : PTag) : ¬ tagLt a a := by unfold tagLt; omega

theorem tagLe_refl (a : PTag) : tagLe a a := Or.inr rfl

theorem tagLt_trans {a b c : PTag} : tagLt a b → tagLt b c → tagLt a c := by
  unfold tagLt; omega

theorem tagLe_trans {a b c : PTag} : tagLe a b → tagLe b c → tagLe a c := by
  rw [tagLe_iff, tagLe_iff, tagLe_iff]; omega

theorem tagLt_of_lt_of_le {a b c : PTag} : tagLt a b → tagLe b c → tagLt a c := by
  rw [tagLe_iff]; unfold tagLt; omega

theorem tagLt_of_le_of_lt {a b c : PTag} : tagLe a b → tagLt b c → tagLt a c := by
  rw [tagLe_iff]; unfold tagLt; omega

theorem tagLe_of_lt {a b : PTag} : tagLt a b → tagLe a b := Or.inl

theorem tagLe_antisymm {a b : PTag} : tagLe a b → tagLe b a → a = b := by
  rw [tagLe_iff, tagLe_iff, tag_eq_iff]; omega

theorem tagLt_or_le (a b : PTag) : tagLt a b ∨ tagLe b a := by
  rw [tagLe_iff]; unfold tagLt; omega

theorem not_tagLt_iff (a b : PTag) : ¬ tagLt a b ↔ tagLe b a := by
  rw [tagLe_iff]; unfold tagLt; omega

theorem not_tagLe_iff (a b : PTag) : ¬ tagLe a b ↔ tagLt b a := by
  rw [tagLe_iff]; unfold tagLt; omega

theorem tagLt_asymm {a b : PTag} : tagLt a b → ¬ tagLt b a := by unfold tagLt; omega

theorem tagLt_ne {a b : PTag} : tagLt a b → a ≠ b := fun h e => by subst e; exact tagLt_irrefl a h

/-- `rmwTag` with the standard literal (Model's `+ 1` elaborates through a generic `OfNat`
instance that `omega` does not read). -/
theorem rmwTag_eq (t : PTag) : rmwTag t = (t.1, t.2.1, t.2.2 + 1) := rfl

/-- An RMW's result tag is above the tag it applies to, and no tag is in between. -/
theorem tagLt_rmwTag (t : PTag) : tagLt t (rmwTag t) := by
  obtain ⟨a, b, c⟩ := t; simp only [tagLt, rmwTag_eq, true_and, and_true]; omega

theorem rmwTag_no_between (t x : PTag) : tagLt t x → tagLt x (rmwTag t) → False := by
  obtain ⟨a, b, c⟩ := t; obtain ⟨d, e, f⟩ := x; simp only [tagLt, rmwTag_eq, true_and, and_true]; omega

theorem rmwTag_mono {a b : PTag} : tagLe a b → tagLe (rmwTag a) (rmwTag b) := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  rw [tagLe_iff, tagLe_iff]; simp only [rmwTag_eq, true_and, and_true]; omega

/-! ## min, max, median -/

/-- The smaller of two tags (as `median3` computes it). -/
def tagMin (a b : PTag) : PTag := if tagLt a b then a else b

theorem median3_eq (a b c : PTag) : median3 a b c = tagMax (tagMin a b) (tagMin (tagMax a b) c) :=
  rfl

theorem tagMax_le_iff {a b t : PTag} : tagLe (tagMax a b) t ↔ tagLe a t ∧ tagLe b t := by
  unfold tagMax; by_cases h : tagLt a b <;> simp only [h, ite_true, ite_false]
  · exact ⟨fun h' => ⟨tagLe_trans (tagLe_of_lt h) h', h'⟩, fun h' => h'.2⟩
  · exact ⟨fun h' => ⟨h', tagLe_trans ((not_tagLt_iff _ _).1 h) h'⟩, fun h' => h'.1⟩

theorem le_tagMax_l (a b : PTag) : tagLe a (tagMax a b) := by
  unfold tagMax; by_cases h : tagLt a b <;> simp only [h, ite_true, ite_false]
  · exact tagLe_of_lt h
  · exact tagLe_refl a

theorem le_tagMax_r (a b : PTag) : tagLe b (tagMax a b) := by
  unfold tagMax; by_cases h : tagLt a b <;> simp only [h, ite_true, ite_false]
  · exact tagLe_refl b
  · exact (not_tagLt_iff _ _).1 h

theorem le_tagMin_iff {a b t : PTag} : tagLe t (tagMin a b) ↔ tagLe t a ∧ tagLe t b := by
  unfold tagMin; by_cases h : tagLt a b <;> simp only [h, ite_true, ite_false]
  · exact ⟨fun h' => ⟨h', tagLe_trans h' (tagLe_of_lt h)⟩, fun h' => h'.1⟩
  · exact ⟨fun h' => ⟨tagLe_trans h' ((not_tagLt_iff _ _).1 h), h'⟩, fun h' => h'.2⟩

theorem tagMin_le_l (a b : PTag) : tagLe (tagMin a b) a := by
  unfold tagMin; by_cases h : tagLt a b <;> simp only [h, ite_true, ite_false]
  · exact tagLe_refl a
  · exact (not_tagLt_iff _ _).1 h

theorem tagMin_le_r (a b : PTag) : tagLe (tagMin a b) b := by
  unfold tagMin; by_cases h : tagLt a b <;> simp only [h, ite_true, ite_false]
  · exact tagLe_of_lt h
  · exact tagLe_refl b

theorem le_tagMax_iff_of {a b t : PTag} (h : tagLe t a ∨ tagLe t b) : tagLe t (tagMax a b) := by
  rcases h with h | h
  · exact tagLe_trans h (le_tagMax_l a b)
  · exact tagLe_trans h (le_tagMax_r a b)

theorem tagMax_mono {a a' b b' : PTag} (ha : tagLe a a') (hb : tagLe b b') :
    tagLe (tagMax a b) (tagMax a' b') :=
  tagMax_le_iff.2 ⟨tagLe_trans ha (le_tagMax_l _ _), tagLe_trans hb (le_tagMax_r _ _)⟩

theorem tagMin_mono {a a' b b' : PTag} (ha : tagLe a a') (hb : tagLe b b') :
    tagLe (tagMin a b) (tagMin a' b') :=
  le_tagMin_iff.2 ⟨tagLe_trans (tagMin_le_l _ _) ha, tagLe_trans (tagMin_le_r _ _) hb⟩

theorem tagMax_mem (a b : PTag) : tagMax a b = a ∨ tagMax a b = b := by
  unfold tagMax; by_cases h : tagLt a b <;> simp [h]

theorem tagMin_mem (a b : PTag) : tagMin a b = a ∨ tagMin a b = b := by
  unfold tagMin; by_cases h : tagLt a b <;> simp [h]

/-- The frontier is one of the three tags. -/
theorem median3_mem (a b c : PTag) : median3 a b c = a ∨ median3 a b c = b ∨ median3 a b c = c := by
  rw [median3_eq]
  rcases tagMax_mem (tagMin a b) (tagMin (tagMax a b) c) with h | h <;> rw [h]
  · rcases tagMin_mem a b with h' | h' <;> simp [h']
  · rcases tagMin_mem (tagMax a b) c with h' | h' <;> rw [h']
    · rcases tagMax_mem a b with h'' | h'' <;> simp [h'']
    · simp

/-- The frontier only grows when a tag grows. -/
theorem median3_mono {a a' b b' c c' : PTag} (ha : tagLe a a') (hb : tagLe b b') (hc : tagLe c c') :
    tagLe (median3 a b c) (median3 a' b' c') := by
  rw [median3_eq, median3_eq]
  exact tagMax_mono (tagMin_mono ha hb) (tagMin_mono (tagMax_mono ha hb) hc)

/-- Two tags at least `t` make the frontier at least `t` (quorum). -/
theorem le_median3_of_two {a b c t : PTag}
    (h : (tagLe t a ∧ tagLe t b) ∨ (tagLe t a ∧ tagLe t c) ∨ (tagLe t b ∧ tagLe t c)) :
    tagLe t (median3 a b c) := by
  rw [median3_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact tagLe_trans (le_tagMin_iff.2 ⟨h1, h2⟩) (le_tagMax_l _ _)
  · exact le_tagMax_iff_of (Or.inr (le_tagMin_iff.2 ⟨tagLe_trans h1 (le_tagMax_l a b), h2⟩))
  · exact le_tagMax_iff_of (Or.inr (le_tagMin_iff.2 ⟨tagLe_trans h1 (le_tagMax_r a b), h2⟩))

end Perennial.gryff.proto
