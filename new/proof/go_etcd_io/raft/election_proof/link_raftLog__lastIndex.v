Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__maybeLastIndex.

Module RaftLogLastIndexPostulates : RAFTLOG__LASTINDEX_POSTULATES.
  Include UnstableMaybeLastIndex.
End RaftLogLastIndexPostulates.

Module RaftLogLastIndex := RaftLogLastIndexProof RaftLogLastIndexPostulates.
