-- dsv-kitgen's scratch axiom check (dropped before the branch's final head).
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.TopLevelRobustness
public import Dsverify.Proof.rabia.examples.rabianet.TopLevelRobustness
public import Dsverify.Proof.raxos.examples.quepaxanet.TopLevelRobustness
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelRobustness
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.TopLevelRobustness

#print axioms Perennial.github_com.xiang90.paxos.examples.paxosnet.paxos_remote_robust
#print axioms Perennial.rabia.examples.rabianet.rabia_remote_robust
#print axioms Perennial.raxos.examples.quepaxanet.quepaxa_remote_robust
#print axioms Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet.swiftpaxos_remote_robust
#print axioms Perennial.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.epaxos_remote_robust
