Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__promotable.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__hasNextOrInProgressSnapshot.

Module Type RAFT__PROMOTABLE_POSTULATES.
  (* [promotable]'s body is
       pr := r.trk.Progress[r.id]
       return pr != nil && !pr.IsLearner &&
              !r.raftLog.hasNextOrInProgressSnapshot()
     so this is the callee.  Declared although the proof is still
     [Admitted]: the dependency is real and the signature is where it
     belongs. *)
  Include RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.
End RAFT__PROMOTABLE_POSTULATES.
