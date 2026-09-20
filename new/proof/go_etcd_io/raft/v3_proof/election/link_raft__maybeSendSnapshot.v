Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__maybeSendSnapshot.

Module RaftMaybeSendSnapshotPostulates : RAFT__MAYBESENDSNAPSHOT_POSTULATES.
End RaftMaybeSendSnapshotPostulates.

Module RaftMaybeSendSnapshot :=
  RaftMaybeSendSnapshotProof RaftMaybeSendSnapshotPostulates.
