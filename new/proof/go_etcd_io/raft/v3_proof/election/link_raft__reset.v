Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__reset.

Module ResetPostulates : RESET_POSTULATES.
End ResetPostulates.

Module Reset := ResetProof ResetPostulates.
