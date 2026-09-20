Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__sendAppend.

Module RaftBcastAppendPostulates : RAFT__BCASTAPPEND_POSTULATES.
  Include ProgressTrackerVisit.
  Include RaftSendAppend.
End RaftBcastAppendPostulates.

Module RaftBcastAppend := RaftBcastAppendProof RaftBcastAppendPostulates.
