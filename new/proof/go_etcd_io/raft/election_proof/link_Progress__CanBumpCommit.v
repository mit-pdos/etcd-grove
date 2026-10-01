Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__CanBumpCommit.

Module ProgressCanBumpCommitPostulates : PROGRESS__CANBUMPCOMMIT_POSTULATES.
End ProgressCanBumpCommitPostulates.

Module ProgressCanBumpCommit :=
  ProgressCanBumpCommitProof ProgressCanBumpCommitPostulates.
