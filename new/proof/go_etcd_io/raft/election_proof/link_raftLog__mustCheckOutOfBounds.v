Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.

Module RaftLogMustCheckOutOfBoundsPostulates : RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES.
  Include RaftLogFirstIndex.
  Include RaftLogLastIndex.
End RaftLogMustCheckOutOfBoundsPostulates.

Module RaftLogMustCheckOutOfBounds := RaftLogMustCheckOutOfBoundsProof RaftLogMustCheckOutOfBoundsPostulates.
