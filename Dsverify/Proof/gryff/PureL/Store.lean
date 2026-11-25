/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/Store.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: the stores (each replica's register `(val, tag)`) and the frontier.

* `Tag.lt_iff`: the model's `Tag.lt` is `tagLt` on `Tag.toP` (signed fields).
* `overwrite_tag`: `HandleOverwrite` only raises the store, to at least the written tag.
* `step_tag_mono` (`StoreSteps.lean`): **a step never lowers the store**.
* `cut_tag_mono`, `front_mono`: along a run the stores and the frontier only grow.
* `median3_le_of_two`: two tags at most `t` make the frontier at most `t` (used by L1).
-/
module

public import Dsverify.Proof.gryff.Pure.LinDefs
public import Dsverify.Proof.gryff.PureL.Run
public import Dsverify.Proof.gryff.Proto.TagOrder
public import Dsverify.Proof.gryff.PureL.StoreSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- Along a run, each replica's store only grows. -/
theorem cut_tag_mono {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    {k k' : Nat} (hkk : k ≤ k') : tagLe (cutSt l k r).tag.toP (cutSt l k' r).tag.toP := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
  clear hkk
  induction d with
  | zero => exact tagLe_refl _
  | succ d ih =>
    rw [← Nat.add_assoc]
    generalize k + d = k' at ih ⊢
    refine tagLe_trans ih ?_
    cases hn : l[k']? with
    | none =>
      have : l.length ≤ k' := by simpa using hn
      have e : l.take (k' + 1) = l.take k' := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      unfold cutSt; rw [e]; exact tagLe_refl _
    | some x =>
      obtain ⟨r', e⟩ := x
      obtain ⟨s', o, hs, h1, h2, -, -⟩ := grun_label h hn
      by_cases hr : r = r'
      · subst hr; rw [h1]; exact step_tag_mono hs
      · rw [h2 r hr]; exact tagLe_refl _

/-- **The frontier only grows** along a run. -/
theorem front_mono {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    {k k' : Nat} (hkk : k ≤ k') : tagLe (front l k) (front l k') :=
  median3_mono (cut_tag_mono h 0 hkk) (cut_tag_mono h 1 hkk) (cut_tag_mono h 2 hkk)

theorem median3_le_of_two {a b c t : PTag}
    (h : (tagLe a t ∧ tagLe b t) ∨ (tagLe a t ∧ tagLe c t) ∨ (tagLe b t ∧ tagLe c t)) :
    tagLe (median3 a b c) t := by
  rw [median3_eq]
  rw [tagMax_le_iff]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨tagLe_trans (tagMin_le_l a b) h1, tagLe_trans (tagMin_le_l _ _) (tagMax_le_iff.2 ⟨h1, h2⟩)⟩
  · refine ⟨tagLe_trans (tagMin_le_l a b) h1, tagLe_trans (tagMin_le_r _ _) h2⟩
  · refine ⟨tagLe_trans (tagMin_le_r a b) h1, tagLe_trans (tagMin_le_r _ _) h2⟩

theorem median3_le_of_pair {l : List Label} {k : Nat} {t : PTag} {w1 w2 : Fin 3} (hne : w1 ≠ w2)
    (h1 : tagLe (cutSt l k w1).tag.toP t) (h2 : tagLe (cutSt l k w2).tag.toP t) :
    tagLe (front l k) t := by
  unfold front
  apply median3_le_of_two
  match w1, w2, hne, h1, h2 with
  | 0, 0, hne, _, _ => exact absurd rfl hne
  | 1, 1, hne, _, _ => exact absurd rfl hne
  | 2, 2, hne, _, _ => exact absurd rfl hne
  | 0, 1, _, h1, h2 => exact Or.inl ⟨h1, h2⟩
  | 1, 0, _, h1, h2 => exact Or.inl ⟨h2, h1⟩
  | 0, 2, _, h1, h2 => exact Or.inr (Or.inl ⟨h1, h2⟩)
  | 2, 0, _, h1, h2 => exact Or.inr (Or.inl ⟨h2, h1⟩)
  | 1, 2, _, h1, h2 => exact Or.inr (Or.inr ⟨h1, h2⟩)
  | 2, 1, _, h1, h2 => exact Or.inr (Or.inr ⟨h2, h1⟩)

end Perennial.gryff.pure
