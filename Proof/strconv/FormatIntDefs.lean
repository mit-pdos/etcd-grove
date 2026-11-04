/-
**`strconv.FormatInt`'s result** (pure): `fmtInt n b`, `n`'s digits in base `b` with a leading `-`
when negative (Go's `strconv.FormatInt`, `internal/strconv/itoa.go`: the unsigned digits of `-n`,
two's complement, after `-`). Lean-first (no Rocq counterpart); K2 of `notes/k8s-compactor-plan.md`
(the compactor's `compact_rev_key` holds `FormatInt(rev, 10)`, which `ParseInt` reads back).
-/
module

public import Proof.strconv.FormatUintDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **`strconv.FormatInt(n, b)`** of a base `2 ≤ b ≤ 36`: `-` (byte 45) and the digits of `-n`
when `n` is negative, else the digits of `n`. -/
def fmtInt (n : w64) (b : w64) : GoString :=
  if sint.Z n < 0 then W8 45 :: fmtUint (-n) b else fmtUint n b

/-- A number below `2 ^ k` has at most `k + 1` digits in a base `b ≥ 2`. -/
theorem baseDigits_length_le (b : Nat) (hb : 2 ≤ b) :
    ∀ (k n : Nat), n < 2 ^ k → (baseDigits b hb n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    rw [baseDigits]
    have : n < b := by simp at hn; omega
    simp [this]
  | succ k ih =>
    intro n hn
    rw [baseDigits]
    split
    · simp
    · have hq : n / b < 2 ^ k := by
        have h2 : n / b ≤ n / 2 := Nat.div_le_div_left hb (by decide)
        rw [Nat.pow_succ] at hn
        omega
      simp only [List.length_append, List.length_singleton]
      have := ih (n / b) hq
      omega

/-- `FormatInt`'s result is short: a sign and 65 digits at most. -/
theorem fmtInt_length_le (n b : w64) : (fmtInt n b).length ≤ 66 := by
  have hu : ∀ m : w64, (fmtUint m b).length ≤ 65 := by
    intro m
    unfold fmtUint
    split
    · rename_i h
      simp only [List.length_map]
      exact baseDigits_length_le b.toNat h 64 m.toNat m.isLt
    · simp
  unfold fmtInt
  split
  · simp only [List.length_cons]; have := hu (-n); omega
  · have := hu n; omega

end EtcdGrove
end Perennial
