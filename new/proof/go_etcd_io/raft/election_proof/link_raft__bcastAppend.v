Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__sendAppend.

Module RaftBcastAppendPostulates : RAFT__BCASTAPPEND_POSTULATES.
  Include ProgressTrackerVisit.
  Include RaftSendAppend.
End RaftBcastAppendPostulates.

Module RaftBcastAppend := RaftBcastAppendProof RaftBcastAppendPostulates.
