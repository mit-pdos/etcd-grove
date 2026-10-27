/-
**Go's semantics: `float64(c)` of an untyped integer constant `c`** (2026-10-27). Lean-first.

Goose emits the comparison `backoff > math.MaxInt64` (client-go's exponential limiter,
`default_rate_limiters.go:125`) with the constant's conversion left to run time,
`Convert go.untypedInt go.float64 #(9223372036854775807 : Int)`, and Perennial's semantics has
conversions of untyped integers to the integer types only (`UntypedIntSemantics`), so it does not
step. In Go the constant is converted at compile time to the nearest `float64` (`2^63` here; the
language specification, "Constants": a constant converted to a floating-point type is rounded).
`UntypedIntToFloat64Semantics` states that it steps, in the shape of Perennial's `float64(n)` of a
typed integer (`Float64Semantics.convert_int_to_float64`, `FloatOps.int64ToFloat64`): to an
uninterpreted function of the integer (floats are opaque in the model; the limiter's spec needs
nothing of the value).

A **hypothesis class** on the semantics in use, like `EtcdGrove.Float64ToInt64Semantics`, not an
axiom: the results that need it take it as an instance argument (`etc/gen-link.py`'s
`SEM_PREMISES`). The general fix (Goose folding the constant conversion, or the step in
Perennial's `UntypedIntSemantics`) is for Perennial (`notes/perennial-changes.md`).
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **`float64(c)` of an untyped integer constant `c`** (a hypothesis on the semantics in use, see
the file header): an uninterpreted function of `c`. -/
class UntypedIntToFloat64Semantics [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] where
  /-- `float64(c)` of the untyped integer `c`: uninterpreted. -/
  untypedIntToFloat64 : Int → w64
  convert_untyped_int_to_float64 (v : Int) :
    go.IsGoStepPureDetTagged under (Convert go.untypedInt go.float64) #v
      (Val #(untypedIntToFloat64 v))

attribute [instance] UntypedIntToFloat64Semantics.convert_untyped_int_to_float64
export UntypedIntToFloat64Semantics (untypedIntToFloat64)

end EtcdGrove
end Perennial
