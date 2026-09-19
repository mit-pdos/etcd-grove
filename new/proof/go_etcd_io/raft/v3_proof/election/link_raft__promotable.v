Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__promotable.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__hasNextOrInProgressSnapshot.

Module RaftPromotablePostulates : RAFT__PROMOTABLE_POSTULATES.
  Include RaftLogHasNextOrInProgressSnapshot.
End RaftPromotablePostulates.

Module RaftPromotable := RaftPromotableProof RaftPromotablePostulates.
