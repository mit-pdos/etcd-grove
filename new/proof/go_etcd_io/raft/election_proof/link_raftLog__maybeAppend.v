Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__maybeAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__findConflict.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__append.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__commitTo.

Module RaftLogMaybeAppendPostulates : RAFTLOG__MAYBEAPPEND_POSTULATES.
  Include RaftLogMatchTerm.
  Include RaftLogFindConflict.
  Include RaftLogAppend.
  Include RaftLogCommitTo.
End RaftLogMaybeAppendPostulates.

Module RaftLogMaybeAppend := RaftLogMaybeAppendProof RaftLogMaybeAppendPostulates.
