Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_logSliceFromMsgApp.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__maybeAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__zeroTermOnOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__findConflictByTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.

Module RaftHandleAppendEntriesPostulates : RAFT__HANDLEAPPENDENTRIES_POSTULATES.
  Include LogSliceFromMsgApp.
  Include RaftLogMaybeAppend.
  Include RaftLogTerm.
  Include RaftLogZeroTermOnOutOfBounds.
  Include RaftLogLastIndex.
  Include RaftLogFindConflictByTerm.
  Include Send.
End RaftHandleAppendEntriesPostulates.

Module RaftHandleAppendEntries := RaftHandleAppendEntriesProof RaftHandleAppendEntriesPostulates.
