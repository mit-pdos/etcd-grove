/-
**`strconv.FormatUint`'s result** (pure): `fmtUint n b`, the digits of `n` in base `b`, most
significant first, without leading zeros (`"0"` for `0`), the digits `0-9` then `a-z` (Go's
`strconv.FormatUint`, `internal/strconv/itoa.go`). Lean-first (no Rocq counterpart). Since the
Perennial pin that proves `FormatUint` (stdlib2, 2026-11-21) these are Perennial's own
(`internal.strconv.fmtUint`, ...), exported here under their old names.

`decStr n = fmtUint n 10`, the decimal form, is injective (`decStr_inj`): the model API server's
resource versions (`examples/k8s/daemonset/apimodel`, `rvString`) are looked up by it.
-/
module

public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

export internal.strconv (baseDigits digitsVal digitsVal_append digitsVal_baseDigits baseDigits_lt
  digitChar digitChar_inj map_digitChar_inj fmtUint fmtInt baseDigits_length_le)

/-- The decimal form of `n` (`strconv.FormatUint(n, 10)`). -/
def decStr (n : w64) : GoString := fmtUint n (W64 10)

theorem decStr_eq (n : w64) :
    decStr n = (baseDigits 10 (by omega) n.toNat).map digitChar := by
  unfold decStr fmtUint
  rfl

/-- **The decimal form is injective.** -/
theorem decStr_inj {m n : w64} (h : decStr m = decStr n) : m = n := by
  rw [decStr_eq, decStr_eq] at h
  have h' := map_digitChar_inj 10 (by omega) _ _ (baseDigits_lt 10 _ m.toNat)
    (baseDigits_lt 10 _ n.toNat) h
  have := congrArg (digitsVal 10) h'
  rw [digitsVal_baseDigits, digitsVal_baseDigits] at this
  exact BitVec.eq_of_toNat_eq this

/-- The decimal form is never empty. -/
theorem decStr_ne_nil (n : w64) : decStr n ≠ [] := by
  rw [decStr_eq, baseDigits]
  split <;> simp

end EtcdGrove
end Perennial
