/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/SortPure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the insertion sort of the trusted `sort.Slice` model (`Harness/Code/sort_extra.lean`)
on `[]int32` with `less = (<)`, as pure invariants: its result is `mergeSort` by `sle`.
-/
module

public import Dsverify.Proof.gryff.Model.Types

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.sortp

open Perennial.gryff.model (sle slt)

/-- Sorted by `sle`. -/
def Srt (l : List w32) : Prop := l.Pairwise (fun a b => sle a b = true)

theorem sle_trans (a b c : w32) (h1 : sle a b = true) (h2 : sle b c = true) : sle a c = true := by
  simp only [sle, decide_eq_true_eq] at *; omega

theorem sle_total (a b : w32) : (sle a b || sle b a) = true := by
  simp only [sle, Bool.or_eq_true, decide_eq_true_eq]; omega

theorem sle_antisymm (a b : w32) (h1 : sle a b = true) (h2 : sle b a = true) : a = b := by
  simp only [sle, sint.Z, decide_eq_true_eq] at h1 h2
  exact BitVec.eq_of_toInt_eq (by omega)

/-- A sorted permutation is `mergeSort`'s. -/
theorem srt_perm_eq (xs ys : List w32) (hs : Srt ys) (hp : ys.Perm xs) :
    ys = xs.mergeSort (fun a b => sle a b) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => sle a b = true)
  · intro a b _ _ h1 h2; exact sle_antisymm a b h1 h2
  · exact hs
  · exact List.pairwise_mergeSort (fun a b c => sle_trans a b c) sle_total xs
  · exact hp.trans (List.mergeSort_perm xs _).symm

/-- The outer loop's invariant at `i` (`i` from 1): a sorted prefix of length `min i n`. -/
def Outer (xs ys : List w32) (i : Nat) : Prop :=
  ys.Perm xs ∧ 1 ≤ i ∧ (i ≤ ys.length ∨ i = 1) ∧
    ∃ srt rest, ys = srt ++ rest ∧ Srt srt ∧ srt.length = min i ys.length

/-- The inner loop's invariant (inserting the element now at `j`; the outer loop at `i`). -/
def Inner (xs ys : List w32) (i j : Nat) : Prop :=
  ys.Perm xs ∧ ∃ pre a post rest, ys = pre ++ a :: (post ++ rest) ∧ pre.length = j ∧
    j + post.length = i ∧ Srt (pre ++ post) ∧ ∀ x ∈ post, slt a x = true

theorem outer_init (xs : List w32) : Outer xs xs 1 := by
  refine ⟨List.Perm.refl _, Nat.le_refl _, Or.inr rfl, xs.take 1, xs.drop 1, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · cases xs with
    | nil => exact List.Pairwise.nil
    | cons a t => simp [Srt]
  · simp

theorem outer_len (xs ys : List w32) (i : Nat) (h : Outer xs ys i) : ys.length = xs.length :=
  h.1.length_eq

theorem inner_init (xs ys : List w32) (i : Nat) (h : Outer xs ys i) (hi : i < ys.length) :
    Inner xs ys i i := by
  obtain ⟨hp, -, -, srt, rest, rfl, hs, hl⟩ := h
  have hl' : srt.length = i := by rw [hl]; omega
  cases rest with
  | nil => simp at hi; omega
  | cons a rest =>
    exact ⟨hp, srt, a, [], rest, by simp, hl', by simp, by simpa using hs, by simp⟩

theorem inner_len (xs ys : List w32) (i j : Nat) (h : Inner xs ys i j) : ys.length = xs.length :=
  h.1.length_eq

theorem inner_lt (xs ys : List w32) (i j : Nat) (h : Inner xs ys i j) : i < ys.length ∧ j ≤ i := by
  obtain ⟨-, pre, a, post, rest, rfl, hl, hj, -, -⟩ := h
  simp; omega

/-- The element read at `j` and at `j - 1`. -/
theorem inner_get (xs ys : List w32) (i j : Nat) (h : Inner xs ys i j) :
    ∃ pre a post rest, ys = pre ++ a :: (post ++ rest) ∧ pre.length = j ∧ ys[j]? = some a ∧
      j + post.length = i ∧ Srt (pre ++ post) ∧ (∀ x ∈ post, slt a x = true) := by
  obtain ⟨-, pre, a, post, rest, rfl, hl, hj, hs, hx⟩ := h
  refine ⟨pre, a, post, rest, rfl, hl, ?_, hj, hs, hx⟩
  rw [List.getElem?_append_right (by omega)]; simp [hl]

theorem inner_get_prev (xs ys : List w32) (i j : Nat) (h : Inner xs ys i j) (hj : 0 < j) :
    ∃ b, ys[j - 1]? = some b := by
  obtain ⟨-, pre, a, post, rest, rfl, hl, -, -, -⟩ := h
  refine ⟨pre[j - 1]'(by omega), ?_⟩
  rw [List.getElem?_append_left (by omega)]; simp

/-- One swap (`s[j], s[j-1] = s[j-1], s[j]` when `s[j] < s[j-1]`). -/
theorem inner_step (xs ys : List w32) (i j : Nat) (h : Inner xs ys i j) (hj : 0 < j)
    (a b : w32) (ha : ys[j]? = some a) (hb : ys[j - 1]? = some b) (hlt : slt a b = true) :
    Inner xs ((ys.set j b).set (j - 1) a) i (j - 1) := by
  obtain ⟨hp, pre, a', post, rest, rfl, hl, hj', hs, hx⟩ := h
  have ha' : a' = a := by
    rw [List.getElem?_append_right (by omega)] at ha; simp [hl] at ha; exact ha
  subst ha'
  obtain ⟨pre', c, rfl⟩ : ∃ pre' c, pre = pre' ++ [c] := by
    refine ⟨pre.dropLast, pre.getLast (List.ne_nil_of_length_pos (by omega)), ?_⟩
    exact (List.dropLast_concat_getLast _).symm
  simp only [List.length_append, List.length_singleton] at hl
  have hc : c = b := by
    rw [List.getElem?_append_left (by simp; omega)] at hb
    rw [List.getElem?_append_right (by omega)] at hb
    have : j - 1 - pre'.length = 0 := by omega
    simp [this] at hb; exact hb
  subst hc
  have e : (((pre' ++ [c]) ++ a' :: (post ++ rest)).set j c).set (j - 1) a' =
      pre' ++ a' :: ((c :: post) ++ rest) := by
    have h1 : ((pre' ++ [c]) ++ a' :: (post ++ rest)) = pre' ++ (c :: a' :: (post ++ rest)) := by simp
    rw [h1, List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
    have h2 : j - pre'.length = 1 := by omega
    have h3 : j - 1 - pre'.length = 0 := by omega
    rw [h2, h3]; simp
  rw [e]
  refine ⟨?_, pre', a', c :: post, rest, rfl, by omega, by simp; omega, ?_, ?_⟩
  · refine List.Perm.trans ?_ hp
    have : pre' ++ a' :: (c :: post ++ rest) = pre' ++ [a', c] ++ (post ++ rest) := by simp
    have h2 : (pre' ++ [c]) ++ a' :: (post ++ rest) = pre' ++ [c, a'] ++ (post ++ rest) := by simp
    rw [this, h2]
    exact List.Perm.append_right _ (List.Perm.append_left _ (List.Perm.swap _ _ _))
  · have : pre' ++ c :: post = (pre' ++ [c]) ++ post := by simp
    rw [this]; exact hs
  · intro x hx'
    simp only [List.mem_cons] at hx'
    rcases hx' with rfl | hx'
    · exact hlt
    · exact hx x hx'

/-- The inner loop's exit: the prefix of length `i + 1` is sorted. -/
theorem inner_done (xs ys : List w32) (i j : Nat) (h : Inner xs ys i j)
    (hstop : j = 0 ∨ ∃ a b, ys[j]? = some a ∧ ys[j - 1]? = some b ∧ slt a b = false) :
    Outer xs ys (i + 1) := by
  obtain ⟨hp, pre, a, post, rest, rfl, hl, hj, hs, hx⟩ := h
  have hsrt : Srt (pre ++ a :: post) := by
    unfold Srt at hs ⊢
    rw [List.pairwise_append] at hs ⊢
    obtain ⟨hpre, hpost, hpp⟩ := hs
    refine ⟨hpre, List.pairwise_cons.2 ⟨fun x hx' => ?_, hpost⟩, ?_⟩
    · have := hx x hx'; simp only [slt, sle, decide_eq_true_eq] at this ⊢; omega
    intro y hy z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · -- y ∈ pre, y ≤ last of pre ≤ a
      rcases hstop with h0 | ⟨a', b, ha, hb, hab⟩
      · subst h0; have : pre = [] := List.eq_nil_of_length_eq_zero hl
        subst this; simp at hy
      have hae : a' = z := by
        rw [List.getElem?_append_right (show pre.length ≤ j by omega)] at ha
        simp [hl] at ha; exact ha.symm
      subst hae
      have hbl : pre[j - 1]? = some b := by
        rwa [List.getElem?_append_left (show j - 1 < pre.length by
          rcases Nat.eq_zero_or_pos j with h | h
          · subst h; have : pre = [] := List.eq_nil_of_length_eq_zero hl
            subst this; simp at hy
          · omega)] at hb
      obtain ⟨hjl, hbe⟩ := List.getElem?_eq_some_iff.1 hbl
      -- every element of `pre` is ≤ its last element `b`
      have hyb : sle y b = true := by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        by_cases hkl : k = j - 1
        · subst hkl; rw [hbe]; simp [sle]
        · have hk' : k < j - 1 := by omega
          have := List.pairwise_iff_getElem.1 hpre k (j - 1) hk hjl hk'
          rw [← hbe]; exact this
      simp only [slt, sle, Bool.eq_false_iff, ne_eq, decide_eq_true_eq] at hab hyb ⊢; omega
    · exact hpp y hy z hz
  refine ⟨hp, by omega, Or.inl ?_, pre ++ a :: post, rest, by simp, hsrt, ?_⟩
  · simp only [List.length_append, List.length_cons]; omega
  · simp only [List.length_append, List.length_cons]; omega

theorem outer_done (xs ys : List w32) (i : Nat) (h : Outer xs ys i) (hi : ys.length ≤ i) :
    ys = xs.mergeSort (fun a b => sle a b) := by
  obtain ⟨hp, -, -, srt, rest, rfl, hs, hl⟩ := h
  have : rest = [] := by
    simp at hl hi; apply List.eq_nil_of_length_eq_zero; omega
  subst this
  simp only [List.append_nil] at hs ⊢
  exact srt_perm_eq xs srt hs (by simpa using hp)

end Perennial.gryff.replica2.sortp
