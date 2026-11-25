/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/NumSteps.lean (lab master 915f964;
namespace `VsrJson` there).
-/
/-
`numL` (scanNumber) by program point, on the suffix at an index (for the Go proof).
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.StrSteps

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JsonScan

open Perennial

theorem dropWhile_eq_drop (p : w8 → Bool) (l : List w8) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  induction l with
  | nil => simp
  | cons c l ih => by_cases h : p c = true <;> simp [List.dropWhile_cons, List.takeWhile_cons, h, ih]

theorem digitsL_eq (l : List w8) (j : Nat) :
    digitsL l j = (j + (l.takeWhile isDig).length, l.dropWhile isDig) := by
  induction l generalizing j with
  | nil => simp [digitsL]
  | cons c l ih =>
    by_cases h : isDig c = true
    · simp [digitsL, h, ih, List.takeWhile_cons, List.dropWhile_cons]; omega
    · simp at h; simp [digitsL, h, List.takeWhile_cons, List.dropWhile_cons]

/-- The end of the digits at `j`. -/
def digEnd (bs : List w8) (j : Nat) : Nat := j + ((bs.drop j).takeWhile isDig).length

theorem digitsL_drop (bs : List w8) (j : Nat) :
    digitsL (bs.drop j) j = (digEnd bs j, bs.drop (digEnd bs j)) := by
  rw [digitsL_eq, dropWhile_eq_drop, List.drop_drop]; rfl

theorem fracL_nil (j : Nat) (eof : Bool) : fracL [] j eof = endS eof j := by simp [fracL]
theorem expL_nil (j : Nat) (eof : Bool) : expL [] j eof = endS eof j := by simp [expL]

theorem intL_eq (l : List w8) (j : Nat) (eof : Bool) :
    intL l j eof = fracL (match l with
      | c :: r => if c = 48#8 then (j + 1, r) else digitsL l j
      | [] => (j, [])).2 (match l with
      | c :: r => if c = 48#8 then (j + 1, r) else digitsL l j
      | [] => (j, [])).1 eof := by
  unfold intL
  cases l with
  | nil => rfl
  | cons c r =>
    dsimp only
    by_cases hc : c = 48#8
    · simp only [hc, if_true, ite_true]; cases r <;> rfl
    · simp only [hc, if_false, ite_false]
      generalize digitsL (c :: r) j = p
      rcases p with ⟨a, _ | ⟨x, t⟩⟩ <;> rfl

theorem fracL_digits (l : List w8) (j : Nat) (eof : Bool) :
    (match (digitsL l j).2 with
      | [] => endS eof (digitsL l j).1
      | r4@(_ :: _) => expL r4 (digitsL l j).1 eof) = expL (digitsL l j).2 (digitsL l j).1 eof := by
  generalize digitsL l j = p
  rcases p with ⟨a, _ | ⟨x, r⟩⟩ <;> rfl

variable (bs : List w8) (eof : Bool)

theorem numL_neg (i : Nat) (h : bs[i]? = some 45#8) :
    numL (bs.drop i) i eof =
      match bs[i + 1]? with
      | none => (1, i + 1)
      | some d => if !isDig d then (2, i + 1) else intL (bs.drop (i + 1)) (i + 1) eof := by
  rw [drop_cons_of bs i _ h]
  simp only [numL, if_true, ite_true]
  cases h1 : bs[i + 1]? with
  | none => rw [List.drop_eq_nil_of_le (by simp at h1; omega)]
  | some d => rw [drop_cons_of bs (i + 1) _ h1]

theorem numL_pos (i : Nat) (c : w8) (h : bs[i]? = some c) (hc : c ≠ 45#8) :
    numL (bs.drop i) i eof = intL (bs.drop i) i eof := by
  rw [drop_cons_of bs i _ h]; simp [numL, hc]

theorem intL_zero (j : Nat) (h : bs[j]? = some 48#8) :
    intL (bs.drop j) j eof = fracL (bs.drop (j + 1)) (j + 1) eof := by
  rw [drop_cons_of bs j _ h, intL_eq]
  simp

theorem intL_dig (j : Nat) (c : w8) (h : bs[j]? = some c) (hc : c ≠ 48#8) :
    intL (bs.drop j) j eof = fracL (bs.drop (digEnd bs j)) (digEnd bs j) eof := by
  have hd := digitsL_drop bs j
  rw [drop_cons_of bs j _ h] at hd ⊢
  rw [intL_eq]
  simp only [hc, if_false, ite_false, hd]

theorem fracL_end (j : Nat) (h : bs.length ≤ j) : fracL (bs.drop j) j eof = endS eof j := by
  rw [List.drop_eq_nil_of_le h]; simp [fracL]

theorem fracL_nodot (j : Nat) (c : w8) (h : bs[j]? = some c) (hc : c ≠ 46#8) :
    fracL (bs.drop j) j eof = expL (bs.drop j) j eof := by
  rw [drop_cons_of bs j _ h]; simp [fracL, hc]

theorem fracL_dot (j : Nat) (h : bs[j]? = some 46#8) :
    fracL (bs.drop j) j eof =
      match bs[j + 1]? with
      | none => (1, j + 1)
      | some d => if !isDig d then (2, j + 1) else
          expL (bs.drop (digEnd bs (j + 1))) (digEnd bs (j + 1)) eof := by
  rw [drop_cons_of bs j _ h]
  simp only [fracL, if_true, ite_true]
  cases h1 : bs[j + 1]? with
  | none => rw [List.drop_eq_nil_of_le (by simp at h1; omega)]
  | some d =>
    have hd := digitsL_drop bs (j + 1)
    rw [drop_cons_of bs (j + 1) _ h1] at hd ⊢
    simp only
    split
    · rfl
    · rw [hd]; dsimp only
      cases hdt : List.drop (digEnd bs (j + 1)) bs <;> rfl

theorem expL_end (j : Nat) (h : bs.length ≤ j) : expL (bs.drop j) j eof = endS eof j := by
  rw [List.drop_eq_nil_of_le h]; simp [expL]

theorem expL_noe (j : Nat) (c : w8) (h : bs[j]? = some c) (hc : ¬ (c = 101#8 ∨ c = 69#8)) :
    expL (bs.drop j) j eof = (0, j) := by
  rw [drop_cons_of bs j _ h]; simp only [expL, hc, if_false, ite_false]

/-- After `e`/`E` and its optional sign, at `j2`. -/
def expAt (j2 : Nat) : Nat × Nat :=
  match bs[j2]? with
  | none => (1, j2)
  | some d => if !isDig d then (2, j2) else
      if bs.length ≤ digEnd bs j2 then endS eof (digEnd bs j2) else (0, digEnd bs j2)

theorem expL_e (j : Nat) (c : w8) (h : bs[j]? = some c) (hc : c = 101#8 ∨ c = 69#8) :
    expL (bs.drop j) j eof =
      expAt bs eof (match bs[j + 1]? with
        | some s => if s = 43#8 ∨ s = 45#8 then j + 2 else j + 1
        | none => j + 1) := by
  rw [drop_cons_of bs j _ h]
  simp only [expL, hc, if_true, ite_true]
  cases h1 : bs[j + 1]? with
  | none =>
    rw [List.drop_eq_nil_of_le (by simp at h1; omega)]
    simp [expAt, h1]
  | some s =>
    rw [drop_cons_of bs (j + 1) _ h1]
    simp only
    have key : ∀ j2 (r : List w8), r = bs.drop j2 →
        (match r with
          | [] => (1, j2)
          | d :: r3 => if !isDig d then (2, j2) else
              match (digitsL (d :: r3) j2).2 with
              | [] => endS eof (digitsL (d :: r3) j2).1
              | _ :: _ => (0, (digitsL (d :: r3) j2).1)) = expAt bs eof j2 := by
      intro j2 r hr
      subst hr
      unfold expAt
      cases h2 : bs[j2]? with
      | none => rw [List.drop_eq_nil_of_le (by simp at h2; omega)]
      | some d =>
        rw [drop_cons_of bs j2 _ h2]
        simp only
        split
        · rfl
        · have hd := digitsL_drop bs j2
          rw [drop_cons_of bs j2 _ h2] at hd
          rw [hd]; simp only
          split
          · rename_i hh; rw [if_pos (by rw [List.drop_eq_nil_iff] at hh; exact hh)]
          · rename_i hh
            have : ¬ bs.length ≤ digEnd bs j2 := by
              intro hc; rw [List.drop_eq_nil_of_le hc] at hh; cases hh
            rw [if_neg this]
    by_cases hs : s = 43#8 ∨ s = 45#8
    · simp only [hs, if_true, ite_true]
      exact key (j + 2) _ rfl
    · simp only [hs, if_false, ite_false]
      exact key (j + 1) _ (by rw [drop_cons_of bs (j + 1) _ h1])

end JsonScan
