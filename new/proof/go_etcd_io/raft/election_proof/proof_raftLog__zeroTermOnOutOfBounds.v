Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__zeroTermOnOutOfBounds.

Module RaftLogZeroTermOnOutOfBoundsProof (P : RAFTLOG__ZEROTERMONOUTOFBOUNDS_POSTULATES) : RAFTLOG__ZEROTERMONOUTOFBOUNDS.
Import P.

  (** The three cases of the premise.  For the two globals, the error is a
      pointer-typed interface ([is_new_error], [base.v]), so both
      comparisons step ([CheckComparable] of a pointer type) and the first
      one that matches returns [0]. *)
  Lemma wp_raftLog__zeroTermOnOutOfBounds : wp_raftLog__zeroTermOnOutOfBounds_body.
  Proof.
    intros_ambient.
    intros l t err.
    wp_start as "#Herr".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    iDestruct "Herr" as "[%Hnil|[Hc|Hu]]".
    - subst err. wp_auto. iApply "HΦ". done.
    - iCombine "Hc ErrCompacted" gives %->.
      destruct HErrCompacted_new as (ty & p & ->).
      wp_auto. rewrite decide_True //. wp_auto.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      iApply "HΦ". iPureIntro. intros Hn. by exfalso.
    - iCombine "Hu ErrUnavailable" gives %->.
      destruct HErrUnavailable_new as (ty & p & ->).
      destruct HErrCompacted_new as (tyc & pc & ->).
      wp_auto.
      case_decide as Hty.
      + (* same dynamic type: compare the pointers *)
        wp_auto. case_bool_decide; wp_auto.
        * iApply "HΦ". iPureIntro. intros Hn. by exfalso.
        * rewrite decide_True //. wp_auto.
          rewrite bool_decide_eq_true_2 //. wp_auto.
          iApply "HΦ". iPureIntro. intros Hn. by exfalso.
      + wp_auto. rewrite decide_True //. wp_auto.
        rewrite bool_decide_eq_true_2 //. wp_auto.
        iApply "HΦ". iPureIntro. intros Hn. by exfalso.
  Qed.

End RaftLogZeroTermOnOutOfBoundsProof.
