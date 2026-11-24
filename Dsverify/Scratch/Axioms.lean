-- Scratch (dsv-vr on the main tree's JSON; deleted after the check): vr's and the landed kits'
-- statements imported together (no "environment already contains"), and their axioms.
import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.Vacuous
import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelRobustness
import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelRobustness
import Dsverify.Proof.rabia.examples.rabianet.TopLevelRobustness
import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.TopLevelRobustness
import Dsverify.Proof.raxos.examples.quepaxanet.TopLevelRobustness
import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.TopLevelRobustness
import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.TopLevelRobustness

#print axioms Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.vr_remote_robust
#print axioms Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet.swiftpaxos_remote_robust
#print axioms Perennial.rabia.examples.rabianet.rabia_remote_robust
#print axioms Perennial.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.epaxos_remote_robust
#print axioms Perennial.raxos.examples.quepaxanet.quepaxa_remote_robust
#print axioms Perennial.github_com.xiang90.paxos.examples.paxosnet.paxos_remote_robust
#print axioms Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.counter_remote_robust
#print axioms Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.typeCodecOk_logs
