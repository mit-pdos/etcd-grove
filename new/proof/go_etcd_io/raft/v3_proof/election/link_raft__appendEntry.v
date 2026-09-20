Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__increaseUncommittedSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceReplicate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__append.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send.

Module RaftAppendEntryPostulates : RAFT__APPENDENTRY_POSTULATES.
  Include RaftLogLastIndex.
  Include RaftIncreaseUncommittedSize.
  Include TraceReplicate.
  Include RaftLogAppend.
  Include Send.
End RaftAppendEntryPostulates.

Module RaftAppendEntry := RaftAppendEntryProof RaftAppendEntryPostulates.
