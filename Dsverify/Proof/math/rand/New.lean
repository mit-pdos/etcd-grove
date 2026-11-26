/-
`New(src)` of a `*rngSource` (with its token, `math.rand.isRngSource`) returns a fresh `*Rand` over
it (`math.rand.ownRngRand`: its points-to persistent, since nothing here writes it; the source's
token moved into it): `math.rand.New.ownSpec`, from Perennial's linked `math.rand.wp_New` (any
`src`: a `*Rand` whose `src` field is `src`), framing the token. A trust-boundary axiom from
dsv-fix4 (mit-pdos/etcd-grove#49 fix 4) until dsv-retire-2 (#49 step 2), when Perennial translated
and proved `New` (review of the axiom: `notes/axiom-review/dsv-fix4/math-rand-rng.md`).
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

/-- `New`'s spec over `isRngSource`/`ownRngRand`: Perennial's, with the source's token framed. -/
theorem math.rand.rng.New_rng :
    math.rand.New.ownSpec (GF := GF) math.rand.isRngSource math.rand.ownRngRand := by
  intro src
  iintro %Φ ⟨_Hinit, Hsrc⟩ HΦ
  iunfold math.rand.isRngSource at Hsrc
  icases Hsrc with ⟨%p, %Hp, Htok⟩
  iapply math.rand.wp_New
  · itrivial
  iintro %r !> ⟨%v, #Hr, %Hv⟩
  iapply HΦ
  iunfold math.rand.ownRngRand
  iexists p, v
  iframe Hr Htok
  ipureintro; rw [Hv, Hp]

end proof

end Perennial
