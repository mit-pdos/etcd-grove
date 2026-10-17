/-
**Trust boundary (Go's semantics): `int64(f)` of a `float64`** (unit N4, 2026-10-17). Lean-first
(no Rocq counterpart).

Perennial's semantics models `float64(n)` of an integer as an uninterpreted function
(`Float64Semantics.convert_int_to_float64` etc.) but not the converse, so a conversion
`int64(f)` does not step. `NewServer` computes the lessor's minimum TTL as
`int64(math.Ceil(minTTL.Seconds()))`. In Go the conversion of a `float64` to an `int64` never
panics: it truncates toward zero, and an out-of-range or `NaN` value gives an
implementation-specific result (the language specification, "Conversions between numeric
types"). This axiom states that much, an uninterpreted function `float64ToInt64` of the operand,
in the shape of Perennial's `float64(n)`. A limitation of Perennial, worked around here; the
general fix (a `convert_float64_to_int64` field of `Float64Semantics`, and the other
float-to-integer conversions) is to be proposed to Perennial on its own (`notes/STATUS.md`,
"unit N4, continued").
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- Go's `int64(f)` of a `float64` `f` (its bits): uninterpreted. -/
opaque float64ToInt64 : w64 → w64

/-- **Trust boundary**: `int64(f)` of a `float64` steps purely to `float64ToInt64 f`. -/
axiom convert_float64_to_int64 [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] (v : w64) :
    go.IsGoStepPureDetTagged under (Convert go.float64 go.int64) #v (Val #(float64ToInt64 v))

attribute [instance] convert_float64_to_int64

end EtcdGrove
end Perennial
