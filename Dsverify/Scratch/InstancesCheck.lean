/-
Scratch (dsv-instances; dropped before the branch's final head): the facts behind the finding on the
`math/rand` `Intn` premise of the rabia and QuePaxa statements (notes/dsv-instances.md).
-/
module

public import Dsverify.Proof.math.rand.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext] [GoLocalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- (1) Since Perennial 47ec64a9d, `math.rand.Assumptions` (a premise of every program's
`Assumptions` in both kits) unfolds `Intn` and `globalRand` to their bodies. -/
theorem scratch_intn_unfolds [h : math.rand.Assumptions] :
    FuncUnfold math.rand.Intn [] math.rand.Intn.impl := h.Intn_unfold
theorem scratch_globalRand_unfolds [h : math.rand.Assumptions] :
    FuncUnfold math.rand.globalRand [] math.rand.globalRand.impl := h.globalRand_unfold

/-- (2) The `isPkgInit pkg_id.math.rand` of the kits' `Intn` premises is the main tree's
`define_is_pkg_init iprop(True)` (`Proof/math/rand/Base.lean`), not Perennial's `isInit`. -/
theorem scratch_mathRand_pkgInit_is_main_trees :
    (inferInstance : IsPkgInit (IProp GF) pkg_id.math.rand) = mathRand_is_pkg_init_inst := rfl

end

#print axioms scratch_intn_unfolds
#print axioms scratch_globalRand_unfolds
#print axioms scratch_mathRand_pkgInit_is_main_trees

end Perennial
