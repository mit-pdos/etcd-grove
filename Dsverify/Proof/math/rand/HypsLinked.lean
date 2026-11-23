/-
`math/rand`'s hypotheses as its functions' proofs (the linking tier, CLAUDE.md "Import tiers"): each
`<F>.wp_proof` is the field of the hypothesis class (`Spec.lean`) that states `<F>.spec`. A proof
file takes the class as an instance argument and uses its fields; only linking modules see these.
-/
module

public import Dsverify.Proof.math.rand.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The specs of `NewSource`, `New` and `Rand.Intn`, for some tokens. -/
theorem math.rand.rands.wp_proof [h : math.rand.Hyps GF] :
    ∃ (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF),
      math.rand.RandSpecs GF isSource ownRand :=
  h.rands
theorem math.rand.Intn.wp_proof [h : math.rand.Hyps GF] : math.rand.Intn.spec (GF := GF) := h.Intn

end proof

end Perennial
