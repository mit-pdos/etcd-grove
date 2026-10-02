Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__handleSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.

Module RaftHandleSnapshotPostulates : RAFT__HANDLESNAPSHOT_POSTULATES.
  Include RaftRestore.
  Include RaftLogLastIndex.
  Include Send.
End RaftHandleSnapshotPostulates.

Module RaftHandleSnapshot := RaftHandleSnapshotProof RaftHandleSnapshotPostulates.
