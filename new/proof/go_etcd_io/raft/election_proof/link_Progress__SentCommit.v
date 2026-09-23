Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__SentCommit.

Module ProgressSentCommitPostulates : PROGRESS__SENTCOMMIT_POSTULATES.
End ProgressSentCommitPostulates.

Module ProgressSentCommit :=
  ProgressSentCommitProof ProgressSentCommitPostulates.
