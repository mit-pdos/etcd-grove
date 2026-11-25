/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/time/Results.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The results of `time`: one theorem per spec of `VsrProof/Spec/time.lean` (stubs at the
freeze: `sorry` until the package's prover proves each).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Time

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.NewReal.wp : time.NewReal.spec (GF := GF) (hG := hG) := time.NewReal.wp_proof
/-- Unprovable as stated: `#(methods time.Time.ty "Now" #t)` has no semantics (an interface
type's method value is not defined; the code calls `MethodResolve time.Time.ty "Now" #t`, which
steps to the dynamic type's method). Proved in the code's form: `time.wp_Now_resolve`. -/
theorem time.Time.Now.wp : time.Time.Now.spec (GF := GF) (hG := hG) := fun t ht => time.wp_Now_resolve t ht
theorem time.NewTimer.wp : time.NewTimer.spec (GF := GF) (hG := hG) := time.NewTimer.wp_proof
theorem time.Timer.Reset.wp : time.Timer.Reset.spec (GF := GF) (hG := hG) := time.Timer.Reset.wp_proof
theorem time.Timer.Done.wp : time.Timer.Done.spec (GF := GF) (hG := hG) := time.Timer.Done.wp_proof
theorem time.Timer.SetState.wp : time.Timer.SetState.spec (GF := GF) (hG := hG) := time.Timer.SetState.wp_proof
theorem time.Timer.State.wp : time.Timer.State.spec (GF := GF) (hG := hG) := time.Timer.State.wp_proof

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
