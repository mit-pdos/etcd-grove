/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/WS/Ports.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit WS: introduction laws of the registry's port and peer facts (`portId`, `peerRole`), for the
producers of `connectRes` (from the registry's `nodeIdIs`).
-/
module

public import Dsverify.Proof.gryff.Proto.WireLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- `portId` is persistent (at every address). -/
instance portId_persistent (γ : GryffNames GF) (a : GoString) (id : w32) :
    Persistent (portId γ a id) := by
  unfold portId; infer_instance

/-- A peer role from the port's id: a replica id above the port's replica's, one of the three. -/
theorem peerRole_intro (γ : GryffNames GF) (a : GoString) (id dst : w32)
    (h : uint.Z dst < uint.Z id ∧ uint.Z id < 3) :
    portId γ a dst ⊢ peerRole γ a id := by
  unfold peerRole
  iintro H
  iexists dst
  iframe H
  ipureintro; exact h

end

end Perennial.gryff
