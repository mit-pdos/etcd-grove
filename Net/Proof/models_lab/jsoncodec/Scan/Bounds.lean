/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/ScanBounds.lean (lab master 915f964;
namespace `VsrJson` there).
-/
/-
Bounds on the scanner's indices: every helper's end is within the input from its start, and a
scalar that is done ends after its first byte.
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.NumSteps
public import Net.Proof.models_lab.jsoncodec.Scan.Steps

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JsonScan

open Perennial

theorem strL_bd (cs : List w8) (k : Nat) :
    k ≤ (strL cs k).2 ∧ (strL cs k).2 ≤ k + cs.length ∧ ((strL cs k).1 = 0 → k + 1 ≤ (strL cs k).2) := by
  induction cs, k using strL.induct <;> rw [strL.eq_def] <;> simp_all <;> (try split) <;> (try simp_all) <;> omega

theorem digitsL_bd (cs : List w8) (j : Nat) :
    j ≤ (digitsL cs j).1 ∧ (digitsL cs j).1 + (digitsL cs j).2.length = j + cs.length := by
  induction cs generalizing j with
  | nil => simp [digitsL]
  | cons c r ih =>
    simp only [digitsL]; split
    · have := ih (j + 1); simp at this ⊢; omega
    · simp

theorem endS_bd (eof : Bool) (j : Nat) : (endS eof j).2 = j := by cases eof <;> rfl

theorem digits_tail_bd (cs : List w8) (j : Nat) (eof : Bool) (k : Nat) (hk : k = j + cs.length) :
    j ≤ (match (digitsL cs j).2 with
      | [] => endS eof (digitsL cs j).1
      | _ :: _ => (0, (digitsL cs j).1)).2 ∧
    (match (digitsL cs j).2 with
      | [] => endS eof (digitsL cs j).1
      | _ :: _ => (0, (digitsL cs j).1)).2 ≤ k := by
  have := digitsL_bd cs j
  generalize digitsL cs j = q at *
  rcases q with ⟨a, _ | ⟨x, t⟩⟩ <;> simp [endS_bd] at * <;> omega

theorem expL_bd (cs : List w8) (j : Nat) (eof : Bool) :
    j ≤ (expL cs j eof).2 ∧ (expL cs j eof).2 ≤ j + cs.length := by
  unfold expL
  rcases cs with _ | ⟨c, r⟩
  · simp [endS_bd]
  simp only
  by_cases he : c = 101#8 ∨ c = 69#8
  · simp only [he, if_true, ite_true]
    rcases r with _ | ⟨s, r'⟩
    · simp
    by_cases hs : s = 43#8 ∨ s = 45#8
    · simp only [hs, if_true, ite_true]
      rcases r' with _ | ⟨d, r3⟩
      · simp
      simp only
      by_cases hd : isDig d = true
      · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false, ite_false]
        have := digits_tail_bd (d :: r3) (j + 2) eof _ rfl
        exact ⟨Nat.le_trans (by omega) this.1, Nat.le_trans this.2 (by simp; omega)⟩
      · simp [hd]
    · simp only [hs, if_false, ite_false]
      by_cases hd : isDig s = true
      · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false, ite_false]
        have := digits_tail_bd (s :: r') (j + 1) eof _ rfl
        exact ⟨Nat.le_trans (by omega) this.1, Nat.le_trans this.2 (by simp; omega)⟩
      · simp [hd]
  · simp [he]

theorem fracL_bd (cs : List w8) (j : Nat) (eof : Bool) :
    j ≤ (fracL cs j eof).2 ∧ (fracL cs j eof).2 ≤ j + cs.length := by
  unfold fracL
  rcases cs with _ | ⟨c, r⟩
  · simp [endS_bd]
  simp only
  by_cases he : c = 46#8
  · simp only [he, if_true, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · simp
    simp only
    by_cases hd : isDig d = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false, ite_false]
      have h1 := digitsL_bd (d :: r') (j + 1)
      generalize digitsL (d :: r') (j + 1) = q at *
      rcases q with ⟨a, _ | ⟨x, t⟩⟩
      · simp [endS_bd] at *; omega
      · have h2 := expL_bd (x :: t) a eof
        simp at *; omega
    · simp [hd]
  · simp only [he, if_false, ite_false]
    have := expL_bd (c :: r) j eof; simpa using this

theorem intL_bd (cs : List w8) (j : Nat) (eof : Bool) :
    j ≤ (intL cs j eof).2 ∧ (intL cs j eof).2 ≤ j + cs.length ∧
      (∀ c r, cs = c :: r → isDig c = true → j + 1 ≤ (intL cs j eof).2) := by
  rw [intL_eq]
  rcases cs with _ | ⟨c, r⟩
  · simp [fracL, endS_bd]
  · simp only
    by_cases h0 : c = 48#8
    · simp only [h0, if_true, ite_true]
      have := fracL_bd r (j + 1) eof
      refine ⟨by omega, by simp; omega, fun _ _ _ _ => by omega⟩
    · simp only [h0, if_false, ite_false]
      have h1 := digitsL_bd (c :: r) j
      have h2 := fracL_bd (digitsL (c :: r) j).2 (digitsL (c :: r) j).1 eof
      refine ⟨by omega, by simp at h1 ⊢; omega, ?_⟩
      rintro c' r' he hd
      cases he
      have : (digitsL (c :: r) j).1 ≥ j + 1 := by simp [digitsL, hd]; have := digitsL_bd r (j+1); omega
      omega

theorem numL_bd (cs : List w8) (i : Nat) (eof : Bool) :
    i ≤ (numL cs i eof).2 ∧ (numL cs i eof).2 ≤ i + cs.length ∧
      (∀ c r, cs = c :: r → (c = 45#8 ∨ isDig c = true) → (numL cs i eof).1 = 0 →
        i + 1 ≤ (numL cs i eof).2) := by
  unfold numL
  rcases cs with _ | ⟨c, r⟩
  · simp
  · simp only
    split
    · rcases r with _ | ⟨d, r'⟩
      · simp
      · simp only; split
        · simp <;> omega
        · rename_i hd
          have := intL_bd (d :: r') (i + 1) eof
          simp at hd
          refine ⟨by omega, by simp at this ⊢; omega, fun _ _ _ _ _ => by omega⟩
    · rename_i h45
      have := intL_bd (c :: r) i eof
      refine ⟨this.1, this.2.1, ?_⟩
      rintro c' r' he hc _
      cases he
      rcases hc with hc | hc
      · exact absurd hc h45
      · exact this.2.2 c r rfl hc

theorem litL_bd (cs : List w8) (j : Nat) (lit : List w8) :
    j ≤ (litL cs j lit).2 ∧ (litL cs j lit).2 ≤ j + cs.length ∧
      ((litL cs j lit).1 = 0 → (litL cs j lit).2 = j + lit.length) := by
  induction cs generalizing j lit with
  | nil => cases lit <;> simp [litL]
  | cons c r ih =>
    cases lit with
    | nil => simp [litL]
    | cons l ls =>
      simp only [litL]; split
      · have := ih (j + 1) ls; simp at this ⊢; omega
      · simp

theorem scalarL_bd (cs : List w8) (i : Nat) (eof : Bool) :
    i ≤ (scalarL cs i eof).2 ∧ (scalarL cs i eof).2 ≤ i + cs.length ∧
      ((scalarL cs i eof).1 = 0 → i + 1 ≤ (scalarL cs i eof).2) := by
  unfold scalarL
  rcases cs with _ | ⟨c, r⟩
  · simp
  · simp only
    split
    · have := strL_bd r (i + 1); simp; omega
    · split
      · rename_i h; have := numL_bd (c :: r) i eof
        exact ⟨this.1, this.2.1, this.2.2 c r rfl h⟩
      · split
        · have := litL_bd (c :: r) i go!"true"; simp at this ⊢; omega
        · split
          · have := litL_bd (c :: r) i go!"false"; simp at this ⊢; omega
          · split
            · have := litL_bd (c :: r) i go!"null"; simp at this ⊢; omega
            · simp

theorem goL_bd (eof : Bool) : ∀ (n : Nat) (cs : List w8), cs.length = n →
    ∀ (i : Nat) (stk : List w8) (st : Nat) (eOK : Bool),
    (goL cs i stk st eOK eof).2 ≤ i + cs.length := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cs hn i stk st eOK
    rcases cs with _ | ⟨c, r⟩
    · rw [goL_nil]; simp
    rw [goL.eq_def]
    simp only [List.length_cons] at hn ⊢
    have IH : ∀ (cs' : List w8), cs'.length < n → ∀ i' stk' st' eOK',
        (goL cs' i' stk' st' eOK' eof).2 ≤ i' + cs'.length :=
      fun cs' h i' stk' st' eOK' => ih cs'.length h cs' rfl i' stk' st' eOK'
    have hs := scalarL_bd (c :: r) i (eof && stk.isEmpty)
    have hstr := strL_bd r (i + 1)
    generalize scalarL (c :: r) i (eof && stk.isEmpty) = P at *
    generalize strL r (i + 1) = Q at *
    simp only [List.length_cons] at hs
    repeat' split
    all_goals first
      | omega
      | exact Nat.le_trans (IH r (by omega) (i + 1) _ _ _) (by omega)
      | exact Nat.le_trans (IH (r.drop (P.2 - i - 1)) (by simp; omega) P.2 _ _ _) (by simp; omega)
      | exact Nat.le_trans (IH (r.drop (Q.2 - i - 1)) (by simp; omega) Q.2 _ _ _) (by simp; omega)
      | skip

theorem scanL_le (bs : List w8) (eof : Bool) : (scanL bs eof).2 ≤ bs.length := by
  have := goL_bd eof bs.length bs rfl 0 [] 0 false
  simpa [scanL] using this

end JsonScan
