(** * Proof: [raft.raft__Step] against its spec

    Opaquely ascribed, so the proof term is sealed: callers can depend on
    nothing but the spec.  The binders arrive by [intros] rather than
    [Context] -- the lemma's type is closed, so there are no section variables
    to discharge and no [Collection W] is needed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step.

Module StepProof (P : STEP_POSTULATES) : STEP.

  Lemma wp_raft__Step : wp_raft__Step_body.
  Proof.
    intros ?????? sem package_sem bytes_sem cfg γ r id s m.
    intros Helection Hhup Hvote Hvoteresp.
    iIntros (Φ) "(#Hinit & Hphys & Hghost & #Hm & #Hctx) HΦ".
    destruct Helection as [Hty | [Hty | Hty]].
    - (* MsgHup: a local message, handled by [hup]. *)
      wp_apply (P.wp_raft__Step_MsgHup with "[$Hphys $Hghost]"); [done|by auto|].
      iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
      iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
      destruct Hst as [sent Hst]. by eexists [], sent.
    - (* MsgVote: answer the vote request, stepping down first if needed. *)
      destruct (Hvote Hty) as (Hto & Hterm & Hfnz).
      iDestruct ("Hm" $! mtype.Vote with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVote. }
      wp_apply (P.wp_raft__Step_MsgVote with "[$Hphys $Hghost $Hm' $Hctx]");
        [done..|].
      iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
      iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
      destruct Hst as (recv & sent & _ & Hstep). by eexists recv, sent.
    - (* MsgVoteResp: tally the vote, possibly winning or losing. *)
      destruct (Hvoteresp Hty) as [Hto Hterm].
      iDestruct ("Hm" $! mtype.VoteResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVoteResp. }
      wp_apply (P.wp_raft__Step_MsgVoteResp with "[$Hphys $Hghost $Hm']"); [done..|].
      iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
      iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
      destruct Hst as (recv & sent & _ & Hstep). by eexists recv, sent.
  Qed.

End StepProof.
