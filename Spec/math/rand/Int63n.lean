/-
`rand.Int63n`, of Go's `math/rand`: Perennial's spec (`math.rand.Int63n.spec`, proved by
`math.rand.wp_Int63n`), restated in this repository's namespace. Lean-first (no Rocq counterpart);
the watch slice's unit W-S (2026-10-14: `GetProgressReportInterval`'s jitter); the trust boundary,
with precondition `True`, until 2026-11-24 (rand-retire), when Perennial's proof (47ec64a9d) replaced
the axiom and the precondition became the package's `isPkgInit` (the global generator's invariant).
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

/-- `rand.Int63n(n)` of a positive `n`: a number in `[0, n)` (Go panics for `n <= 0`). -/
abbrev rand.Int63n.spec : Prop :=
  ∀ n : w64,
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand ∗ ⌜0 < sint.Z n⌝ }}
    (App (Val (@! _root_.Perennial.math.rand.Int63n)) (Val #n))
  {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
