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

end EtcdGrove
end Perennial
