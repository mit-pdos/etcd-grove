/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/vsrkv/Results.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The results of `vsrkv`: one theorem per spec of `VsrProof/Spec/vsrkv.lean` (stubs at the
freeze: `sorry` until the package's prover proves each).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrkv
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrkv.Store

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : vsrkv.Assumptions]

theorem vsrkv.New.wp : vsrkv.New.spec (GF := GF) (hG := hG) := vsrkv.New.wp_proof
theorem vsrkv.Store.Handle.wp : vsrkv.Store.Handle.spec (GF := GF) (hG := hG) := vsrkv.Store.Handle.wp_proof
theorem vsrkv.Store.Handle_value.wp : vsrkv.Store.Handle_value.spec (GF := GF) (hG := hG) := vsrkv.Store.Handle_value.wp_proof

end results

end Perennial.github_com.tangledbytes.go_vsr.examples
