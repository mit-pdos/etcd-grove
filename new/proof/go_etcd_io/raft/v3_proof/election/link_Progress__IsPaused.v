Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Progress__IsPaused.

Module ProgressIsPausedPostulates : PROGRESS__ISPAUSED_POSTULATES.
End ProgressIsPausedPostulates.

Module ProgressIsPaused := ProgressIsPausedProof ProgressIsPausedPostulates.
