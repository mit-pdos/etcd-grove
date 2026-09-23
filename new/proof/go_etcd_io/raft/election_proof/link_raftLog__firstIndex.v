Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__maybeFirstIndex.

Module RaftLogFirstIndexPostulates : RAFTLOG__FIRSTINDEX_POSTULATES.
  Include UnstableMaybeFirstIndex.
End RaftLogFirstIndexPostulates.

Module RaftLogFirstIndex := RaftLogFirstIndexProof RaftLogFirstIndexPostulates.
