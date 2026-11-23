/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Client.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client node's spec (stage 2): `ClientNodeOk` for any package states from the callees' specs
is `cnode.client_node_ok_of` (Proof/swiftnet/ClientNode.lean); at the run's package states,
`client_node_ok` (Proof/swiftnet/ClientNodeLink.lean). Stage 1's `ClientOk` assembly
(`client_ok_of`, `ClientHyps`) is gone with `ClientOk`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNode
