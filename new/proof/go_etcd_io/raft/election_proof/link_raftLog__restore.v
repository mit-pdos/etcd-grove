Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__restore.

Module RaftLogRestorePostulates : RAFTLOG__RESTORE_POSTULATES.
  Include UnstableRestore.
End RaftLogRestorePostulates.

Module RaftLogRestore := RaftLogRestoreProof RaftLogRestorePostulates.
