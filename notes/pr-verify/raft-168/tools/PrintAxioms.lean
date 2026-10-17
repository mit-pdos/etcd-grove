import Proof.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResultWithDifference
import Proof.go_etcd_io.raft.v3.quorum.JointConfig__VoteResultWithDifference
import Proof.go_etcd_io.raft.v3.quorum.MajorityConfig__OneLessThanQuorum
import Proof.go_etcd_io.raft.v3.tracker.ProgressTracker__TallyVotesWithDifference
import Proof.go_etcd_io.raft.v3.confchange.Restore
import Proof.go_etcd_io.raft.v3.confchange.Changer__LeaveJoint
import Proof.go_etcd_io.raft.v3.confchange.checkInvariants
import Proof.go_etcd_io.raft.v3.tracker.ProgressTracker__ConfState
import Proof.go_etcd_io.raft.v3.tracker.Config__Clone
open Perennial EtcdGrove
#print axioms quorum.MajorityConfig.VoteResultWithDifference.wp_proof
#print axioms quorum.JointConfig.VoteResultWithDifference.wp_proof
#print axioms quorum.MajorityConfig.OneLessThanQuorum.wp_proof
#print axioms tracker.ProgressTracker.TallyVotesWithDifference.wp_proof
#print axioms confchange.Restore.wp_proof
#print axioms confchange.Changer.LeaveJoint.wp_proof
#print axioms confchange.checkInvariants.wp_proof
#print axioms tracker.ProgressTracker.ConfState.wp_proof
#print axioms tracker.Config.Clone.wp_proof
