Require Export New.proof.go_etcd_io.raft.election_proof.proof_unstable__restore.

Module UnstableRestorePostulates : UNSTABLE__RESTORE_POSTULATES.
End UnstableRestorePostulates.

Module UnstableRestore := UnstableRestoreProof UnstableRestorePostulates.
