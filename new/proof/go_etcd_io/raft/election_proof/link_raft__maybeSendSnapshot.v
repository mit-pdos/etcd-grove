Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__snapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_IsEmptySnap.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.

Module RaftMaybeSendSnapshotPostulates : RAFT__MAYBESENDSNAPSHOT_POSTULATES.
  Include RaftLogSnapshot.
  Include RaftLogFirstIndex.
  Include IsEmptySnap.
  Include ProgressBecomeSnapshot.
  Include Send.
End RaftMaybeSendSnapshotPostulates.

Module RaftMaybeSendSnapshot :=
  RaftMaybeSendSnapshotProof RaftMaybeSendSnapshotPostulates.
