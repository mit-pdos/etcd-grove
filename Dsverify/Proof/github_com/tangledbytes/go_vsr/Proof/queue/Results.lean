/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/queue/Results.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The results of `queue`: one theorem per spec of `VsrProof/Spec/queue.lean` (stubs at the
freeze: `sorry` until the package's prover proves each).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Queue

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : queue.Assumptions]

theorem queue.New.wp : queue.New.spec (GF := GF) (hG := hG) := queue.New.wp_proof
theorem queue.Queue.Push.wp : queue.Queue.Push.spec (GF := GF) (hG := hG) := queue.Queue.Push.wp_proof
theorem queue.Queue.Pop.wp : queue.Queue.Pop.spec (GF := GF) (hG := hG) := queue.Queue.Pop.wp_proof

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
