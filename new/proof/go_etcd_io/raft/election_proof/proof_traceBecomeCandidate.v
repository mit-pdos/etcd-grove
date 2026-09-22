Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceBecomeCandidate.

Module TraceBecomeCandidateProof (P : TRACEBECOMECANDIDATE_POSTULATES) : TRACEBECOMECANDIDATE.

  Lemma wp_traceBecomeCandidate : wp_traceBecomeCandidate_body.
  Proof.
    intros_ambient.
    intros r rs ro pri.
   wp_start as "Hm". by iApply "HΦ".
  Qed.

End TraceBecomeCandidateProof.
