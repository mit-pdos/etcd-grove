Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__append.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__truncateAndAppend.

Module RaftLogAppendPostulates : RAFTLOG__APPEND_POSTULATES.
  Include RaftLogLastIndex.
  Include UnstableTruncateAndAppend.
End RaftLogAppendPostulates.

Module RaftLogAppend := RaftLogAppendProof RaftLogAppendPostulates.
