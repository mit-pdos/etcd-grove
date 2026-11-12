/-
**Go's semantics: `int64(f)` of a `float64`** (unit N4, 2026-10-17; restated 2026-10-18). Lean-first
(no Rocq counterpart).

Perennial's semantics models `float64(n)` of an integer as an uninterpreted function
(`FloatOps.int64ToFloat64`, its step in `Float64Semantics.convert_int_to_float64`) but not the
converse, so a conversion `int64(f)` does not step. `NewServer` computes the lessor's minimum TTL
as `int64(math.Ceil(minTTL.Seconds()))`. In Go the conversion of a `float64` to an `int64` never
panics: it truncates toward zero, and an out-of-range or `NaN` value gives an
implementation-specific result (the language specification, "Conversions between numeric
types"). `Float64ToInt64Semantics` states that much, in the shape of Perennial's `float64(n)`: an
uninterpreted function of the operand (a field, as `FloatOps`'s are) to which the conversion steps.

It is a **hypothesis class**, like Perennial's `go.Semantics`, not an axiom: it constrains the
local context of the semantics in use, and the results that need it (`NewServer.wp_proof`, and its
`Link.lean` result `wp_NewServer`) take it as an instance argument, as they take `go.Semantics`; a
closed theorem takes it as a premise on the initial state's local context (D19a: a pure fact about
Go's semantics). Until 2026-10-18 it was an axiom stated for **every** `GoLocalContext`, which is
inconsistent: at Perennial's default context (`fun _ _ _ => False`) `IsGoStepPureDet`'s
`is_go_step_pure _ _ = Eq e` is `False` (`notes/audit.md`, the first false axiom). A limitation of
Perennial, worked around here; the general fix (the conversion's function in `FloatOps` and its
step in `Float64Semantics`, with the other float-to-integer conversions) is to be proposed to
Perennial on its own (`notes/decisions.md`, "`int64(f)`: a hypothesis class").
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **Go's `int64(f)` of a `float64` `f`** (a hypothesis on the semantics in use, see the file
header): it steps purely to `float64ToInt64 f`, an uninterpreted function of `f`'s bits. -/
class Float64ToInt64Semantics [GooseExts] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] where
  /-- `int64(f)` of the `float64` with bits `f`: uninterpreted. -/
  float64ToInt64 : w64 → w64
  convert_float64_to_int64 (v : w64) :
    go.IsGoStepPureDetTagged under (Convert go.float64 go.int64) #v (Val #(float64ToInt64 v))

attribute [instance] Float64ToInt64Semantics.convert_float64_to_int64
export Float64ToInt64Semantics (float64ToInt64)

end EtcdGrove
end Perennial
