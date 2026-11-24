/-
Pure models of two `jsoncodec` loops that the generated encoders run on a `MarshalJSON` method's
output (`jencValue`): `AppendCompact`'s (`cmpRun`: its final string state, or `none` where it
panics or drops a byte) and `Nesting`'s (`nestRun`: its result, the deepest nesting of arrays and
objects outside strings), with the lemmas for a plain string (`JsonScan.plainEnc` bytes) and
digits. Ported from dsverify-lab's `GoEnc.lean` (`cmpRun`, lab master 915f964); `nestRun` is new
(dsv-vr round 9). Pure.
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Lits

@[expose] public section

namespace Perennial

namespace models_lab.jsoncodec

/-! ## `AppendCompact` -/

/-- A byte `AppendCompact` rejects inside a string. -/
def cmpBad (c : w8) : Bool :=
  decide (c = 60#8 ∨ c = 62#8 ∨ c = 38#8 ∨ c = 92#8 ∨ 128 ≤ c.toNat)

/-- `AppendCompact`'s loop from state `st` (in a string) over `l`: its final state, or `none`
if it panics or drops a byte (whitespace outside strings). -/
def cmpRun : Bool → List w8 → Option Bool
  | st, [] => some st
  | true, c :: r => if cmpBad c then none else cmpRun (decide (c ≠ 34#8)) r
  | false, c :: r => if JsonScan.spB c then none else cmpRun (decide (c = 34#8)) r

theorem cmpRun_append (st : Bool) (l1 l2 : List w8) :
    cmpRun st (l1 ++ l2) = (cmpRun st l1).bind (fun s => cmpRun s l2) := by
  induction l1 generalizing st with
  | nil => simp [cmpRun]
  | cons c r ih =>
    cases st
    · simp only [List.cons_append, cmpRun]; split
      · rfl
      · exact ih _
    · simp only [List.cons_append, cmpRun]; split
      · rfl
      · exact ih _

theorem cmpRun_body (s rest : List w8) (h : ∀ c ∈ s, JsonScan.plainEnc c) :
    cmpRun true (s ++ rest) = cmpRun true rest := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    have hc := h c (by simp)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
    have hb : cmpBad c = false := by
      simp only [cmpBad, decide_eq_false_iff_not]
      intro hh
      rcases hh with e | e | e | e | e
      all_goals first | omega | (subst e; simp_all)
    have hq : decide (c ≠ 34#8) = true := by
      simp only [ne_eq, decide_eq_true_eq]; intro e; subst e; simp_all
    simp only [List.cons_append, cmpRun, hb, hq]
    exact ih (fun c hc => h c (by simp [hc]))

/-- A plain string, in quotes, leaves `AppendCompact` outside strings. -/
theorem cmpRun_str (s rest : List w8) (h : ∀ c ∈ s, JsonScan.plainEnc c) :
    cmpRun false (34#8 :: (s ++ 34#8 :: rest)) = cmpRun false rest := by
  have : JsonScan.spB 34#8 = false := by decide
  simp only [cmpRun, this]
  simp only [decide_true, Bool.false_eq_true, ↓reduceIte]
  rw [cmpRun_body s _ h]
  simp [cmpRun, cmpBad]

theorem decN_plainEnc (n : Nat) : ∀ c ∈ JsonScan.decN n, JsonScan.plainEnc c := by
  intro c hc
  have := JsonScan.decN_digits n c hc
  simp only [JsonScan.isDig, Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at this
  simp only [JsonScan.plainEnc]
  have h1 : (48#8 : w8).toNat = 48 := rfl
  have h2 : (57#8 : w8).toNat = 57 := rfl
  omega

/-! ## `Nesting` -/

/-- `Nesting`'s loop over `l` from its state (`depth`, `max`, in a string): its result. A
backslash in a string skips the next byte. -/
def nestRun : w64 → w64 → Bool → List w8 → w64
  | _, m, _, [] => m
  | d, m, true, c :: r =>
    if c = 92#8 then (match r with
      | [] => m
      | _ :: r' => nestRun d m true r')
    else if c = 34#8 then nestRun d m false r else nestRun d m true r
  | d, m, false, c :: r =>
    if c = 34#8 then nestRun d m true r
    else if c = 91#8 ∨ c = 123#8 then
      nestRun (d + 1) (if uint.Z (d + 1) > uint.Z m then d + 1 else m) false r
    else if c = 93#8 ∨ c = 125#8 then nestRun (d - 1) m false r
    else nestRun d m false r

/-- A plain string's contents leave `Nesting` in the string. -/
theorem nestRun_body (d m : w64) (s rest : List w8) (h : ∀ c ∈ s, JsonScan.plainEnc c) :
    nestRun d m true (s ++ rest) = nestRun d m true rest := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    obtain ⟨h1, h2, h3, h4, -⟩ := h c (by simp)
    have h92 : c ≠ 92#8 := by intro e; subst e; simp_all
    have h34 : c ≠ 34#8 := by intro e; subst e; simp_all
    rw [List.cons_append, nestRun.eq_def]
    simp only [h92, h34, ↓reduceIte]
    exact ih (fun c hc => h c (by simp [hc]))

/-- A plain string, in quotes, leaves `Nesting`'s state as it was. -/
theorem nestRun_str (d m : w64) (s rest : List w8) (h : ∀ c ∈ s, JsonScan.plainEnc c) :
    nestRun d m false (34#8 :: (s ++ 34#8 :: rest)) = nestRun d m false rest := by
  rw [nestRun.eq_def]
  simp only [↓reduceIte]
  rw [nestRun_body d m s _ h, nestRun.eq_def]
  simp only [show (34#8 : w8) ≠ 92#8 by decide, ↓reduceIte]

/-- Bytes that are not `"`, brackets or braces leave `Nesting`'s state as it was. -/
theorem nestRun_plain (d m : w64) (s rest : List w8)
    (h : ∀ c ∈ s, c ≠ 34#8 ∧ c ≠ 91#8 ∧ c ≠ 123#8 ∧ c ≠ 93#8 ∧ c ≠ 125#8) :
    nestRun d m false (s ++ rest) = nestRun d m false rest := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h c (by simp)
    rw [List.cons_append, nestRun.eq_def]
    simp only [h1, h2, h3, h4, h5, or_self, ↓reduceIte]
    exact ih (fun c hc => h c (by simp [hc]))

end models_lab.jsoncodec
end Perennial
