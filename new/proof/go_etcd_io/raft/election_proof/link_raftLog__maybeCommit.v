Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__commitTo.

Module RaftLogMaybeCommitPostulates : RAFTLOG__MAYBECOMMIT_POSTULATES.
  Include RaftLogMatchTerm.
  Include RaftLogCommitTo.
End RaftLogMaybeCommitPostulates.

Module RaftLogMaybeCommit := RaftLogMaybeCommitProof RaftLogMaybeCommitPostulates.
