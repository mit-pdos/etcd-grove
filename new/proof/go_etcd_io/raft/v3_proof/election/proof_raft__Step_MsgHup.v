(** * Proof: [raft.raft__Step_MsgHup] against its spec

    Opaquely ascribed, so the proof term is sealed: callers can depend on
    nothing but the spec.  The binders arrive by [intros] rather than
    [Context] -- the lemma's type is closed, so there are no section variables
    to discharge and no [Collection W] is needed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step_MsgHup.

Module StepMsgHupProof (P : STEP_MSGHUP_POSTULATES) : STEP_MSGHUP.

  Lemma wp_raft__Step_MsgHup : wp_raft__Step_MsgHup_body.
  Proof.
    intros ?????? sem package_sem cfg γ r id s m.
    intros Hty Hterm.
    wp_start as "@".
    iNamed "Hphys".
    wp_auto.
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    (* [m.Term = 0] (a local message), so the term preamble is skipped. *)
    rewrite Hterm !bool_decide_eq_true_2 //.
    wp_auto.
    (* the type switch selects the [MsgHup] case *)
    rewrite Hty /MsgHup bool_decide_eq_true_2 //.
    wp_auto.
    (* no pre-vote, so this is a plain [hup(campaignElection)] *)
    rewrite HnoPreVote. wp_auto.
    (* re-seal the physical ownership for [hup] *)
    iAssert (own_raft_phys γ r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { rewrite /own_raft_phys. iFrame "∗#%". }
    wp_apply (P.wp_raft__hup with "[$Hphys $Hghost]") as "%s' (Hphys & Hghost & %Hstep)".
    { done. }
    iApply ("HΦ" $! interface.nil s'). by iFrame.
  Qed.

End StepMsgHupProof.
