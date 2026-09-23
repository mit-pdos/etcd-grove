Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__increaseUncommittedSize.

Module RaftIncreaseUncommittedSizeProof
  (P : RAFT__INCREASEUNCOMMITTEDSIZE_POSTULATES) :
  RAFT__INCREASEUNCOMMITTEDSIZE.
Import P.

  Lemma wp_raft__increaseUncommittedSize :
    wp_raft__increaseUncommittedSize_body.
  Proof.
    intros_ambient.
    intros cfg r id s es ents dq.
    intros Hzero. wp_start as "H". iNamed "H". iNamed "Hphys". wp_auto.
    (* [payloadsSize] pins the result only for an all-empty batch, which is
       the premise here (it was widened on 2026-09-20 for [maybeSendAppend],
       so the zero comes back as an implication). *)
    wp_apply (wp_payloadsSize with "[$Hes]") as "%psz [Hes %Hpsz]".
    rewrite (Hpsz Hzero).
    (* [s] is [0], so the *middle* conjunct of the reject test is false
       whatever [r.uncommittedSize] is -- but [&&] is a nest of [if]s and
       [wp_auto] parks on the outermost one, which reads a field it knows
       nothing about.  Split on it; both branches fall through to the
       increment. *)
    case_bool_decide as Hunc; wp_auto; (iApply "HΦ"; iFrame "Hes";
      iApply (own_raft_phys_intro with
        "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
      done).
  Qed.

End RaftIncreaseUncommittedSizeProof.
