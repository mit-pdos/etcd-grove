-- Scratch (dsv-steps63): `#print axioms` of the dsverify kits' closed theorems and Net's remote
-- counter. Dropped before the branch's final head.
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.TopLevelRobustness
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelRobustness
public import Dsverify.Proof.raxos.examples.quepaxanet.TopLevelRobustness
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.TopLevelRobustness
public import Dsverify.Proof.rabia.examples.rabianet.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.TopLevelRobustness

open Perennial

#check @github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.epaxos_remote_robust.spec
#print axioms github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.epaxos_remote_robust
#print axioms github_com.imdea_software.swiftpaxos.examples.swiftnet.swiftpaxos_remote_robust
#print axioms raxos.examples.quepaxanet.quepaxa_remote_robust
#print axioms github_com.xiang90.paxos.examples.paxosnet.paxos_remote_robust
#print axioms rabia.examples.rabianet.rabia_remote_robust
#print axioms github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.counter_remote_robust
#check @github_com.imdea_software.swiftpaxos.examples.swiftnet.swiftpaxos_remote_robust.spec
