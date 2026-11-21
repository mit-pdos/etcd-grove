/-
**A member id's string** (rafthttp stage 5d): `types.ID.String`'s result,
`strconv.FormatUint(uint64(id), 16)`, the id in lowercase hexadecimal without leading zeros
(`"0"` for `0`). Pure. A plain path segment (`path.plainSeg`: non-empty, neither `/` nor `.`) and
ASCII: what the stream's path (`streamPath`) and the logs and metrics' labels need.
-/
module

public import Proof.path.Segs
public import Proof.unicode.utf8.Valid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- A hexadecimal digit `d < 16`, lowercase. -/
def types.hexDigit (d : Nat) : w8 := if d < 10 then W8 (48 + d) else W8 (87 + d)

/-- `n` in hexadecimal, most significant digit first, with fuel `f`. -/
def types.hexNatF : Nat → Nat → List w8
  | 0, _ => []
  | f + 1, n => if n < 16 then [types.hexDigit n] else types.hexNatF f (n / 16) ++ [types.hexDigit (n % 16)]

/-- **`id.String()`**: `strconv.FormatUint(uint64(id), 16)`. -/
def types.idStr (id : w64) : GoString := types.hexNatF (id.toNat + 1) id.toNat

example : types.idStr (W64 0) = go!"0" := by decide
example : types.idStr (W64 255) = go!"ff" := by decide
example : types.idStr (W64 0x8e9e05c52164694d) = go!"8e9e05c52164694d" := by decide

theorem types.hexDigit_range (d : Nat) (h : d < 16) :
    (48 ≤ (types.hexDigit d).toNat ∧ (types.hexDigit d).toNat ≤ 57) ∨
    (97 ≤ (types.hexDigit d).toNat ∧ (types.hexDigit d).toNat ≤ 102) := by
  unfold types.hexDigit
  split
  · left; constructor <;> simp <;> omega
  · right; constructor <;> simp <;> omega

theorem types.hexNatF_digits (f n : Nat) :
    ∀ b ∈ types.hexNatF f n, ∃ d, d < 16 ∧ b = types.hexDigit d := by
  induction f generalizing n with
  | zero => simp [types.hexNatF]
  | succ f ih =>
    intro b hb
    simp only [types.hexNatF] at hb
    split at hb
    · simp at hb; exact ⟨n, by omega, hb⟩
    · simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | hb
      · exact ih _ b hb
      · exact ⟨n % 16, Nat.mod_lt _ (by decide), hb⟩

/-- `hexNatF` of a number below `16 ^ (k + 1)` has at most `k + 1` digits. -/
theorem types.hexNatF_length (f n k : Nat) (hk : n < 16 ^ (k + 1)) :
    (types.hexNatF f n).length ≤ k + 1 := by
  induction f generalizing n k with
  | zero => simp [types.hexNatF]
  | succ f ih =>
    simp only [types.hexNatF]
    split
    · simp
    · rename_i hn
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        have h2 : n / 16 < 16 ^ (k + 1) := by
          rw [Nat.div_lt_iff_lt_mul (by decide)]
          rw [Nat.pow_succ] at hk; exact hk
        simp only [List.length_append, List.length_singleton]
        have := ih (n / 16) k h2
        omega

/-- A member id's string has at most 16 digits. -/
theorem types.idStr_length (id : w64) : (types.idStr id).length ≤ 16 :=
  types.hexNatF_length _ _ 15 (lt_of_lt_of_eq id.isLt (by rfl))

theorem types.hexNatF_ne_nil (f n : Nat) (hf : 1 ≤ f) : types.hexNatF f n ≠ [] := by
  cases f with
  | zero => omega
  | succ f => simp only [types.hexNatF]; split <;> simp

/-- A member id's string is a plain path segment. -/
theorem types.idStr_plain (id : w64) : path.plainSeg (types.idStr id) := by
  refine ⟨types.hexNatF_ne_nil _ _ (by omega), fun c hc => ?_⟩
  obtain ⟨d, hd, rfl⟩ := types.hexNatF_digits _ _ c hc
  have := types.hexDigit_range d hd
  constructor <;> intro h <;> have := congrArg BitVec.toNat h <;> simp [path.slash, path.dot] at * <;>
    omega

/-- A member id's string is ASCII. -/
theorem types.idStr_ascii (id : w64) : asciiStr (types.idStr id) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := types.hexNatF_digits _ _ c hc
  have := types.hexDigit_range d hd
  omega

/-- A hexadecimal digit's value (the inverse of `hexDigit` on `d < 16`). -/
def types.hexDigitVal (b : w8) : Nat := if b.toNat < 58 then b.toNat - 48 else b.toNat - 87

/-- A list of hexadecimal digits' value, most significant first. -/
def types.hexVal (l : List w8) : Nat := l.foldl (fun acc b => acc * 16 + types.hexDigitVal b) 0

theorem types.hexDigitVal_hexDigit (d : Nat) (h : d < 16) : types.hexDigitVal (types.hexDigit d) = d := by
  unfold types.hexDigitVal types.hexDigit
  split <;> split <;> simp_all <;> omega

theorem types.hexVal_append_one (l : List w8) (b : w8) :
    types.hexVal (l ++ [b]) = types.hexVal l * 16 + types.hexDigitVal b := by
  simp [types.hexVal, List.foldl_append]

/-- `hexNatF` with enough fuel spells `n`. -/
theorem types.hexVal_hexNatF (f n : Nat) (hf : n < f) : types.hexVal (types.hexNatF f n) = n := by
  induction f generalizing n with
  | zero => omega
  | succ f ih =>
    simp only [types.hexNatF]
    split
    · rename_i h
      simp [types.hexVal, types.hexDigitVal_hexDigit n h]
    · rename_i h
      rw [types.hexVal_append_one, ih (n / 16) (by omega),
        types.hexDigitVal_hexDigit _ (Nat.mod_lt _ (by decide))]
      omega

/-- **Distinct ids, distinct strings**: `ID.String` (`strconv.FormatUint(id, 16)`) is injective. -/
theorem types.idStr_inj (a b : w64) (h : types.idStr a = types.idStr b) : a = b := by
  have ha := types.hexVal_hexNatF (a.toNat + 1) a.toNat (by omega)
  have hb := types.hexVal_hexNatF (b.toNat + 1) b.toNat (by omega)
  unfold types.idStr at h
  rw [h] at ha
  exact BitVec.eq_of_toNat_eq (ha.symm.trans hb)

end EtcdGrove
end Perennial
