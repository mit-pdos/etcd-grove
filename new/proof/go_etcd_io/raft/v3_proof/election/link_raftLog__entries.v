Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__entries.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__slice.

Module RaftLogEntriesPostulates : RAFTLOG__ENTRIES_POSTULATES.
  Include RaftLogLastIndex.
  Include RaftLogSlice.
End RaftLogEntriesPostulates.

Module RaftLogEntries := RaftLogEntriesProof RaftLogEntriesPostulates.
