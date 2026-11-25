-- Scratch (dsv-vr round 11; deleted after the check): vr's and the landed kits'
-- statements imported together (no "environment already contains"), and their axioms.
import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Link
import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelRobustness
import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.NonVacuityLinked
import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelRobustness
import Dsverify.Proof.rabia.examples.rabianet.TopLevelRobustness
import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.TopLevelRobustness
import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.TopLevelRobustness
import Dsverify.Proof.gryff.examples.gryffnet.TopLevelRobustness
import Proof.encoding.json.Codec.NewEncoder
import Proof.encoding.json.Codec.Encoder__Encode_conn

#print axioms Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.vr_remote_robust
#print axioms Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.instances.nonvacuous_premises
#print axioms Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet.swiftpaxos_remote_robust
#print axioms Perennial.rabia.examples.rabianet.rabia_remote_robust
#print axioms Perennial.github_com.xiang90.paxos.examples.paxosnet.paxos_remote_robust
#print axioms Perennial.encoding.json.NewEncoder.wp_proof
#print axioms Perennial.encoding.json.Encoder.Encode_conn.wp_proof
#print axioms Perennial.EtcdGrove.dsvvr.encEncodeConn
#print axioms Perennial.net.resErr_errOrNil
