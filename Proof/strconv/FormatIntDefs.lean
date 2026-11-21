/-
**`strconv.FormatInt`'s result** (pure): `fmtInt n b` (Perennial's `internal.strconv.fmtInt`, exported by
`FormatUintDefs`), `n`'s digits in base `b` with a leading `-`
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
