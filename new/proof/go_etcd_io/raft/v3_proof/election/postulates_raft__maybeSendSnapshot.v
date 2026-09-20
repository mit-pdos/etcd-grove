Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__maybeSendSnapshot.

(** Direct callees: [raftLog.snapshot], [IsEmptySnap],
    [Progress.BecomeSnapshot], [raftLog.firstIndex] (inside a [Debugf]) and
    [raft.send].  None is listed while the proof is [Admitted]; see
    [proof_raft__maybeSendSnapshot.v]. *)
Module Type RAFT__MAYBESENDSNAPSHOT_POSTULATES.
End RAFT__MAYBESENDSNAPSHOT_POSTULATES.
