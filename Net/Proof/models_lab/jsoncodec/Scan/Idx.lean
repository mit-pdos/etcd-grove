/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/ScanIdx.lean (lab master 915f964;
namespace `VsrJson` there).
-/
/-
The scanner's loop on the suffix at an index (for the Go proof of `Scan`).
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.Bounds

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JsonScan

open Perennial

theorem mem_takeWhile' (p : w8 → Bool) (l : List w8) : ∀ c ∈ l.takeWhile p, p c = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro c hc
    by_cases h : p x = true
    · simp [List.takeWhile_cons, h] at hc
      rcases hc with rfl | hc
      · exact h
      · exact ih c hc
    · simp [List.takeWhile_cons, h] at hc

theorem dropWhile_head' (p : w8 → Bool) (l : List w8) (c : w8) (t : List w8)
    (h : l.dropWhile p = c :: t) : p c = false := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    by_cases hx : p x = true
    · simp [List.dropWhile_cons, hx] at h; exact ih h
    · simp [List.dropWhile_cons, hx] at h; rw [← h.1]; simpa using hx

/-- The index after the whitespace at `i`. -/
def skipEnd (bs : List w8) (i : Nat) : Nat := i + ((bs.drop i).takeWhile spB).length

theorem goL_spaces' (ws cs : List w8) (hws : ∀ c ∈ ws, spB c = true) (i : Nat) (stk : List w8)
    (st : Nat) (eOK eof : Bool) :
    goL (ws ++ cs) i stk st eOK eof = goL cs (i + ws.length) stk st eOK eof := by
  induction ws generalizing i with
  | nil => simp
  | cons c ws ih =>
    simp only [List.cons_append]
    rw [goL_space (hc := hws c (by simp)), ih (fun x hx => hws x (by simp [hx]))]
    congr 1; simp; omega

theorem goL_skip (bs : List w8) (i : Nat) (stk : List w8) (st : Nat) (eOK eof : Bool) :
    goL (bs.drop i) i stk st eOK eof =
      goL (bs.drop (skipEnd bs i)) (skipEnd bs i) stk st eOK eof := by
  have e : bs.drop i = (bs.drop i).takeWhile spB ++ (bs.drop i).dropWhile spB :=
    (List.takeWhile_append_dropWhile).symm
  conv => lhs; rw [e]
  rw [goL_spaces' _ _ (mem_takeWhile' spB _), dropWhile_eq_drop, List.drop_drop]
  rfl

theorem skipEnd_le (bs : List w8) (i : Nat) (h : i ≤ bs.length) : skipEnd bs i ≤ bs.length := by
  have := (List.takeWhile_prefix spB (l := bs.drop i)).length_le
  simp [skipEnd] at *; omega

theorem skipEnd_ns (bs : List w8) (i : Nat) (c : w8) (h : bs[skipEnd bs i]? = some c) :
    spB c = false := by
  have e : bs.drop i = (bs.drop i).takeWhile spB ++ (bs.drop i).dropWhile spB :=
    (List.takeWhile_append_dropWhile).symm
  have h2 : (bs.drop i).dropWhile spB = bs.drop (skipEnd bs i) := by
    rw [dropWhile_eq_drop, List.drop_drop]; rfl
  rw [drop_cons_of bs _ c h] at h2
  exact dropWhile_head' spB _ c _ h2

theorem drop_after (bs : List w8) (j p : Nat) (h : j + 1 ≤ p) :
    (bs.drop (j + 1)).drop (p - j - 1) = bs.drop p := by
  rw [List.drop_drop]; congr 1; omega

theorem goL_scalar_idx (bs : List w8) (i : Nat) (stk : List w8) (eOK eof : Bool) (c : w8)
    (hc : bs[i]? = some c) (hs : spB c = false) (h1 : c ≠ 91#8) (h2 : c ≠ 123#8)
    (h3 : ¬(c = 93#8 ∧ eOK = true ∧ stk.head? = some 91#8)) :
    goL (bs.drop i) i stk 0 eOK eof =
      (if (scalarL (bs.drop i) i (eof && stk.isEmpty)).1 ≠ 0 then
        scalarL (bs.drop i) i (eof && stk.isEmpty)
      else if stk = [] then (0, (scalarL (bs.drop i) i (eof && stk.isEmpty)).2)
      else goL (bs.drop (scalarL (bs.drop i) i (eof && stk.isEmpty)).2)
        (scalarL (bs.drop i) i (eof && stk.isEmpty)).2 stk 1 false eof) := by
  have hb := scalarL_bd (bs.drop i) i (eof && stk.isEmpty)
  rw [drop_cons_of bs i c hc] at hb ⊢
  conv => lhs; rw [goL.eq_def]
  simp only [hs, Bool.false_eq_true, if_false, ite_false, if_true, ite_true, h1, h2, false_or]
  rw [if_neg h3]
  generalize scalarL (c :: bs.drop (i + 1)) i (eof && stk.isEmpty) = P at *
  by_cases hP : P.1 = 0
  · simp only [hP, ne_eq, not_true_eq_false, if_false, ite_false]
    split
    · rfl
    · rw [drop_after bs i P.2 (hb.2.2 hP)]
  · simp [hP]

theorem goL_bad1 (c top : w8) (r stk : List w8) (i : Nat) (eOK eof : Bool) (hs : spB c = false)
    (h44 : c ≠ 44#8) (hcl : ¬((c = 93#8 ∧ top = 91#8) ∨ (c = 125#8 ∧ top = 123#8))) :
    goL (c :: r) i (top :: stk) 1 eOK eof = (2, i) := by
  rw [goL.eq_def]; simp only [hs, h44, Bool.false_eq_true, if_false, ite_false]
  simp only [show (1 : Nat) ≠ 0 by decide, if_true, ite_true, if_false, ite_false]
  rw [if_neg hcl]

theorem goL_bad3 (c : w8) (r stk : List w8) (i : Nat) (eOK eof : Bool) (hs : spB c = false)
    (h58 : c ≠ 58#8) : goL (c :: r) i stk 3 eOK eof = (2, i) := by
  rw [goL.eq_def]; simp [hs, h58]

theorem goL_bad2 (c : w8) (r stk : List w8) (i : Nat) (eOK eof : Bool) (hs : spB c = false)
    (hcl : ¬(c = 125#8 ∧ eOK = true)) (h34 : c ≠ 34#8) : goL (c :: r) i stk 2 eOK eof = (2, i) := by
  rw [goL.eq_def]; simp only [hs, Bool.false_eq_true, if_false, ite_false]
  simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_true, ite_true,
    if_false, ite_false]
  rw [if_neg hcl]; simp [h34]

/-! ## Statuses are 0, 1 or 2 -/

theorem digits_tail_st (cs : List w8) (j : Nat) (eof : Bool) :
    (match (digitsL cs j).2 with
      | [] => endS eof (digitsL cs j).1
      | _ :: _ => (0, (digitsL cs j).1)).1 ≤ 2 := by
  generalize digitsL cs j = q
  rcases q with ⟨a, _ | ⟨x, t⟩⟩ <;> cases eof <;> simp [endS]

theorem expL_st (cs : List w8) (j : Nat) (eof : Bool) : (expL cs j eof).1 ≤ 2 := by
  unfold expL
  rcases cs with _ | ⟨c, r⟩
  · cases eof <;> simp [endS]
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
        exact digits_tail_st _ _ eof
      · simp [hd]
    · simp only [hs, if_false, ite_false]
      by_cases hd : isDig s = true
      · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false, ite_false]
        exact digits_tail_st _ _ eof
      · simp [hd]
  · simp [he]
theorem fracL_st (cs : List w8) (j : Nat) (eof : Bool) : (fracL cs j eof).1 ≤ 2 := by
  unfold fracL
  rcases cs with _ | ⟨c, r⟩
  · cases eof <;> simp [endS]
  simp only
  by_cases he : c = 46#8
  · simp only [he, if_true, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · simp
    simp only
    by_cases hd : isDig d = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false, ite_false]
      generalize digitsL (d :: r') (j + 1) = q
      rcases q with ⟨a, _ | ⟨x, t⟩⟩
      · cases eof <;> simp [endS]
      · exact expL_st _ _ _
    · simp [hd]
  · simp only [he, if_false, ite_false]; exact expL_st _ _ _
theorem intL_st (cs : List w8) (j : Nat) (eof : Bool) : (intL cs j eof).1 ≤ 2 := by
  rw [intL_eq]; exact fracL_st _ _ _
theorem numL_st (cs : List w8) (j : Nat) (eof : Bool) : (numL cs j eof).1 ≤ 2 := by
  unfold numL; (repeat' split) <;> simp [intL_st]
theorem strL_st (cs : List w8) (k : Nat) : (strL cs k).1 ≤ 2 := by
  induction cs, k using strL.induct <;> rw [strL.eq_def] <;> simp_all <;> (repeat' split) <;> simp_all
theorem litL_st (cs : List w8) (j : Nat) (lit : List w8) : (litL cs j lit).1 ≤ 2 := by
  induction cs generalizing j lit with
  | nil => cases lit <;> simp [litL]
  | cons c r ih => cases lit with
    | nil => simp [litL]
    | cons l ls => simp only [litL]; split <;> simp [ih]
theorem scalarL_st (cs : List w8) (i : Nat) (eof : Bool) : (scalarL cs i eof).1 ≤ 2 := by
  unfold scalarL; (repeat' split) <;> simp [strL_st, numL_st, litL_st]

end JsonScan
