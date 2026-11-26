/-
`NewSource(seed)` returns a fresh `*rngSource` with its token (`math.rand.isRngSource`,
`RngDefs.lean`): `math.rand.NewSource.ownSpec`, from Perennial's linked `math.rand.wp_NewSource`
(whose post is `isRngSource`'s body). A trust-boundary axiom from dsv-fix4 (mit-pdos/etcd-grove#49
fix 4) until dsv-retire-2 (#49 step 2), when Perennial translated and proved `NewSource`, `newSource`,
`rngSource.Seed` and `seedrand` (review of the axiom: `notes/axiom-review/dsv-fix4/math-rand-rng.md`).
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

/-- `NewSource`'s spec over `isRngSource`: Perennial's. -/
theorem math.rand.rng.NewSource_rng : math.rand.NewSource.ownSpec (GF := GF) math.rand.isRngSource :=
  math.rand.wp_NewSource

end proof

end Perennial
