/-
`rand.Int31`, of Go's `math/rand`: Perennial's spec (`math.rand.Int31.spec`, proved by
`math.rand.wp_Int31`), restated in this repository's namespace. Lean-first (no Rocq counterpart);
traceutil-log (2026-11-23: `traceutil`'s `logInfo` draws the trace's id); the trust boundary, with
precondition `True`, until 2026-11-24 (rand-retire), when Perennial's proof (47ec64a9d) replaced the
axiom and the precondition became the package's `isPkgInit` (the global generator's invariant).
-/
module

public import Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `rand.Int31()`: a non-negative `int32` (Go's documentation: "a non-negative pseudo-random 31-bit
integer as an int32"; the top-level source, safe for concurrent use). -/
abbrev rand.Int31.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
    (App (Val (@! _root_.Perennial.math.rand.Int31)) (Val #()))
  {{ (x : w32), RET #x; ⌜0 ≤ sint.Z x⌝ }}

end spec

end EtcdGrove
end Perennial
