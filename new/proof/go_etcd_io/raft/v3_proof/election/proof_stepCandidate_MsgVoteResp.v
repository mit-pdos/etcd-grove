Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepCandidate_MsgVoteResp.

Module StepCandidateProof (P : STEPCANDIDATE_POSTULATES) : STEPCANDIDATE.

  Lemma wp_stepCandidate_MsgVoteResp : wp_stepCandidate_MsgVoteResp_body.
  Proof.
  Admitted.

End StepCandidateProof.
