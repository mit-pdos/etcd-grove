/-
`(*rngSource).Int63()`, with the source's token, returns a non-negative `int64` and keeps the token:
Perennial's linked `math.rand.rngSource.wp_Int63` (`rngTok` is Perennial's `ownRngSource`). Used
(with `New.lean`, `NewSource.lean`) to prove `(*Rand).Intn` over `ownRngRand` (`RandsLinked.lean`).
A trust-boundary axiom from dsv-fix4 (mit-pdos/etcd-grove#49 fix 4) until dsv-retire-2 (#49 step 2),
when Perennial translated and proved `rngSource`'s `Int63` and `Uint64` (review of the axiom:
`notes/axiom-review/dsv-fix4/math-rand-rng.md`).
-/
module

public import Dsverify.Proof.math.rand.RngDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

/-- `(*rngSource).Int63`'s spec over `rngTok`: Perennial's. -/
theorem math.rand.rng.rngSource_Int63_rng : ∀ (p : Loc),
  {{ math.rand.rngTok (GF := GF) p }}
    (App (Val (p @!! go.GoType.PointerType math.rand.rngSource.ty @!! go!"Int63")) (Val #()))
  {{ (x : w64), RET #x; math.rand.rngTok p ∗ ⌜0 ≤ sint.Z x⌝ }} :=
  math.rand.rngSource.wp_Int63

end proof

end Perennial
