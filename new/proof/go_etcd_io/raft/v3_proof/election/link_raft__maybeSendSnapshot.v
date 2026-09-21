Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__snapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_IsEmptySnap.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__BecomeSnapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send.

Module RaftMaybeSendSnapshotPostulates : RAFT__MAYBESENDSNAPSHOT_POSTULATES.
  Include RaftLogSnapshot.
  Include RaftLogFirstIndex.
  Include IsEmptySnap.
  Include ProgressBecomeSnapshot.
  Include Send.
End RaftMaybeSendSnapshotPostulates.

Module RaftMaybeSendSnapshot :=
  RaftMaybeSendSnapshotProof RaftMaybeSendSnapshotPostulates.
