Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeLastIndex.

Module RaftLogLastIndexPostulates : RAFTLOG__LASTINDEX_POSTULATES.
  Include UnstableMaybeLastIndex.
End RaftLogLastIndexPostulates.

Module RaftLogLastIndex := RaftLogLastIndexProof RaftLogLastIndexPostulates.
