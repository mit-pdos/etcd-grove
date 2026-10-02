Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_logSliceFromMsgApp.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__maybeAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__zeroTermOnOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__findConflictByTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

(** [handleAppendEntries]'s direct callees: [logSliceFromMsgApp], then
    [raftLog.maybeAppend], and on the reject path [raftLog.term],
    [raftLog.zeroTermOnOutOfBounds] (inside the [Debugf]'s arguments),
    [raftLog.lastIndex] and [raftLog.findConflictByTerm]; [send] on every
    exit. *)
Module Type RAFT__HANDLEAPPENDENTRIES_POSTULATES.
  Include LOGSLICEFROMMSGAPP.
  Include RAFTLOG__MAYBEAPPEND.
  Include RAFTLOG__TERM.
  Include RAFTLOG__ZEROTERMONOUTOFBOUNDS.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__FINDCONFLICTBYTERM.
  Include SEND.
End RAFT__HANDLEAPPENDENTRIES_POSTULATES.
