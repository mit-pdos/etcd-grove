Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__findConflict.
Require Export New.proof.go_etcd_io.raft.election_proof.link_pbEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__zeroTermOnOutOfBounds.

Module RaftLogFindConflictPostulates : RAFTLOG__FINDCONFLICT_POSTULATES.
  Include PbEntryID.
  Include RaftLogMatchTerm.
  Include RaftLogLastIndex.
  Include RaftLogTerm.
  Include RaftLogZeroTermOnOutOfBounds.
End RaftLogFindConflictPostulates.

Module RaftLogFindConflict := RaftLogFindConflictProof RaftLogFindConflictPostulates.
