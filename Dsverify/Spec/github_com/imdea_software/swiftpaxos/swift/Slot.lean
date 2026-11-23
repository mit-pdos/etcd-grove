/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Slot.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The SwiftPaxos protocol's slot (HUBS.md): what the hubs (`Spec/swiftnet/Interface.lean`) name
of the protocol, and nothing else. The predicates below are sealed (`@[no_expose]`, R5): an
importer uses them through `Inv.lean`'s laws (intro/elim of the protocols, one law per
method of the method specs, the invariant's laws, the shares' elimination), not their bodies. The definitions and their laws are in `Spec/swift/Inv.lean`
(the invariant's design: its header and `Spec/swift/Model.lean`'s); a hub names only:

* `sp.Names`: the protocol's ghost names;
* `sp.inP γ γc γm`, `sp.outQ γ γc γm`: the wire protocols of a replica's peer-and-client port
  (what its dialers, peers and clients, write; what it writes back);
* `sp.masterSpec γc γm`, `sp.replicaRpcSpec γc γm`: the rpc services' method specs (the master's
  `Register`, `GetLeader`, `GetReplicaList`; a replica's `BeTheLeader`, `Ping`);
* `sp.inv γ γc γm γl`: the protocol's invariant (persistent);
* `sp.clientsStart γ`, `sp.replicaStart γ k`: the client node's and replica node `k`'s shares;
* `sp.alloc`: their allocation at the start.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
