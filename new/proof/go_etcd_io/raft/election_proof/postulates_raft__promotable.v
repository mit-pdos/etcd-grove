Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__promotable.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__hasNextOrInProgressSnapshot.

Module Type RAFT__PROMOTABLE_POSTULATES.
  (* [promotable]'s body is
       pr := r.trk.Progress[r.id]
       return pr != nil && !pr.IsLearner &&
              !r.raftLog.hasNextOrInProgressSnapshot()
     so this is the only callee. *)
  Include RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.
End RAFT__PROMOTABLE_POSTULATES.
