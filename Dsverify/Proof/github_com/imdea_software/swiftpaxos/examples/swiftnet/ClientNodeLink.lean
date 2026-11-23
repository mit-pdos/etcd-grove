/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`ClientNodeOk pkgStates`**: `client_node_ok_of` at the run's package states (`pkgStates`,
Proof/swiftnet/PkgState.lean), from the client node's callees' specs (`ClientNodeHyps`: other
groups' specs, ClientNode.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.PkgState

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- **`ClientNodeOk`** at the run's package states, from the callees' specs. -/
def client_node_ok [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
    (H : cnode.ClientNodeHyps pkgStates) : ClientNodeOk pkgStates :=
  cnode.client_node_ok_of pkgStates H

end Perennial.github_com.imdea_software.swiftpaxos
