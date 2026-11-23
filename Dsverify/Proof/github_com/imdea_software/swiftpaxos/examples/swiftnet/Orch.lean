/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Orch.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`OrchOk pkgStates`**: the orchestrator's spec at node 0 for the run's package states, from
`orch_ok_of` (Proof/swiftnet/OrchSpec.lean) and group C's initializers (`adapter.swiftInits`,
Proof/swiftnet/ClientPkgInits.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchSpec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientPkgInits

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- **`OrchOk`** at the run's package states. -/
theorem orch_ok [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF] : OrchOk pkgStates :=
  orch_ok_of pkgStates (fun _ _ _ _ => adapter.swiftInits)

end Perennial.github_com.imdea_software.swiftpaxos
