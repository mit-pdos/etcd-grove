Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__zeroTermOnOutOfBounds.

Module RaftLogZeroTermOnOutOfBoundsProof (P : RAFTLOG__ZEROTERMONOUTOFBOUNDS_POSTULATES) : RAFTLOG__ZEROTERMONOUTOFBOUNDS.
Import P.

  Lemma wp_raftLog__zeroTermOnOutOfBounds : wp_raftLog__zeroTermOnOutOfBounds_body.
  Proof.
    intros_ambient.
    intros l t err ->.
    wp_start as "_". wp_auto.

    by iApply "HΦ".
  Qed.

End RaftLogZeroTermOnOutOfBoundsProof.
