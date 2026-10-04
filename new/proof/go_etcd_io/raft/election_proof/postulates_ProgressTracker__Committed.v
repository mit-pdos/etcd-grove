Require Export New.proof.go_etcd_io.raft.election_proof.spec_ProgressTracker__Committed.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_matchAckIndexer__AckedIndex.

(** Direct callee: [JointConfig.CommittedIndex], at the tracker's own
    indexer; [matchAckIndexer.AckedIndex]'s triple is what builds the
    [is_AckedIndexer] contract it takes. *)
Module Type PROGRESSTRACKER__COMMITTED_POSTULATES.
  Include JOINTCONFIG__COMMITTEDINDEX.
  Include MATCHACKINDEXER__ACKEDINDEX.
End PROGRESSTRACKER__COMMITTED_POSTULATES.
