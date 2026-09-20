Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.

Module RaftLogMustCheckOutOfBoundsPostulates : RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES.
  Include RaftLogFirstIndex.
  Include RaftLogLastIndex.
End RaftLogMustCheckOutOfBoundsPostulates.

Module RaftLogMustCheckOutOfBounds := RaftLogMustCheckOutOfBoundsProof RaftLogMustCheckOutOfBoundsPostulates.
