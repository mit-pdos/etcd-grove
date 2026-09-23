Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__entries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__slice.

Module RaftLogEntriesPostulates : RAFTLOG__ENTRIES_POSTULATES.
  Include RaftLogLastIndex.
  Include RaftLogSlice.
End RaftLogEntriesPostulates.

Module RaftLogEntries := RaftLogEntriesProof RaftLogEntriesPostulates.
