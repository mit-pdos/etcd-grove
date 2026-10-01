Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__term.

Module RaftLogMatchTermPostulates : RAFTLOG__MATCHTERM_POSTULATES.
  Include RaftLogTerm.
End RaftLogMatchTermPostulates.

Module RaftLogMatchTerm := RaftLogMatchTermProof RaftLogMatchTermPostulates.
