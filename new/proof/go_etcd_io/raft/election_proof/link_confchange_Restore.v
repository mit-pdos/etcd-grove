Require Export New.proof.go_etcd_io.raft.election_proof.proof_confchange_Restore.

Module ConfchangeRestorePostulates : CONFCHANGE_RESTORE_POSTULATES.
End ConfchangeRestorePostulates.

Module ConfchangeRestore := ConfchangeRestoreProof ConfchangeRestorePostulates.
