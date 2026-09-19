Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__term.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.

Module RaftLogTermPostulates : RAFTLOG__TERM_POSTULATES.
  Include UnstableMaybeTerm.
  Include RaftLogFirstIndex.
  Include RaftLogLastIndex.
End RaftLogTermPostulates.

Module RaftLogTerm := RaftLogTermProof RaftLogTermPostulates.
