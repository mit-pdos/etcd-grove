Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__commitTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.

Module RaftLogCommitToPostulates : RAFTLOG__COMMITTO_POSTULATES.
  Include RaftLogLastIndex.
End RaftLogCommitToPostulates.

Module RaftLogCommitTo := RaftLogCommitToProof RaftLogCommitToPostulates.
