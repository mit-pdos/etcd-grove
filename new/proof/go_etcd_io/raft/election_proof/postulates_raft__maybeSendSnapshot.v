Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__snapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_IsEmptySnap.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

(** Direct callees: [raftLog.snapshot], [IsEmptySnap],
    [Progress.BecomeSnapshot], [raftLog.firstIndex] (inside the third
    [Debugf]'s argument list) and [raft.send].  The three [Debugf] calls go
    through [wp_Logger__logf] ([inv_logger.v]), which is not a collection. *)
Module Type RAFT__MAYBESENDSNAPSHOT_POSTULATES.
  Include RAFTLOG__SNAPSHOT.
  Include RAFTLOG__FIRSTINDEX.
  Include ISEMPTYSNAP.
  Include PROGRESS__BECOMESNAPSHOT.
  Include SEND.
End RAFT__MAYBESENDSNAPSHOT_POSTULATES.
