Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__append.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__truncateAndAppend.

Module RaftLogAppendPostulates : RAFTLOG__APPEND_POSTULATES.
  Include RaftLogLastIndex.
  Include UnstableTruncateAndAppend.
End RaftLogAppendPostulates.

Module RaftLogAppend := RaftLogAppendProof RaftLogAppendPostulates.
