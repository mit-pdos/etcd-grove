/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/assert/Results.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The results of `assert`: one theorem per spec of `VsrProof/Spec/assert.lean` (stubs at the
freeze: `sorry` until the package's prover proves each).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : assert.Assumptions]

theorem assert.Assert.wp : assert.Assert.spec (GF := GF) (hG := hG) := fun format args => by
  wp_start
  wp_auto
  wp_end

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
