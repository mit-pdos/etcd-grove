Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeFirstIndex.

Module RaftLogFirstIndexPostulates : RAFTLOG__FIRSTINDEX_POSTULATES.
  Include UnstableMaybeFirstIndex.
End RaftLogFirstIndexPostulates.

Module RaftLogFirstIndex := RaftLogFirstIndexProof RaftLogFirstIndexPostulates.
