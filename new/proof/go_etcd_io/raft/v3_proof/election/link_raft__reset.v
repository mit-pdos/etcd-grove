Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__reset.

Module ResetPostulates : RESET_POSTULATES.
End ResetPostulates.

Module Reset := ResetProof ResetPostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments Reset.wp_raft__reset {_ _ _ _ _ _ _ _}.
