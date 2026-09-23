Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.link_limitSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_entsSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_extend.

Module RaftLogSlicePostulates : RAFTLOG__SLICE_POSTULATES.
  Include RaftLogMustCheckOutOfBounds.
  Include UnstableSlice.
  Include LimitSize.
  Include EntsSize.
  Include Extend.
End RaftLogSlicePostulates.

Module RaftLogSlice := RaftLogSliceProof RaftLogSlicePostulates.
