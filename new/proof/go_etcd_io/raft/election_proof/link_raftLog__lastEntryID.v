Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__term.

Module RaftLogLastEntryIDPostulates : RAFTLOG__LASTENTRYID_POSTULATES.
  Include RaftLogLastIndex.
  Include RaftLogTerm.
End RaftLogLastEntryIDPostulates.

Module RaftLogLastEntryID := RaftLogLastEntryIDProof RaftLogLastEntryIDPostulates.
