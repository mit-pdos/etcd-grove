(** The three per-message-type lemmas are **proof structure, not
    specification**.  [Step] is one Go function and therefore has exactly one
    spec, in [spec_raft__Step.v]; giving each branch its own [Module Type]
    would put four Hoare triples for [r.Step] in four files, which is the
    thing this layout exists to prevent.  Since 2026-09-17 the branches live
    in files of their own -- functors over [STEP_POSTULATES] with no
    signature -- so that [make -j] checks them in parallel; only this file
    may [Require] them, and the ascription below is still the only thing any
    other file can see.

    Since 2026-09-18 those eight files sit in **[proof_raft__Step_helpers/]**,
    because [Step] is the only function here whose proof needs more than one
    file and having them at the top level broke the four-files-per-function
    pattern the election directory is meant to be audited by.  The directory
    is [proof_<fn>_helpers/] and not [proof_<fn>/] because the latter would
    collide with this file in Rocq's logical namespace.
    [etc/check-module-discipline.py] enforces both halves: a helper at the
    top level is an error, and a [Module Type] inside a helpers directory is
    an error. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_helpers.proof_raft__Step_MsgHup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_helpers.proof_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_helpers.proof_raft__Step_MsgVoteResp.

Module StepProof (P : STEP_POSTULATES) : STEP.

Module H := StepMsgHup P.
Module V := StepMsgVote P.
Module R := StepMsgVoteResp P.
(** [wp_raft__Step]'s type is closed, so the prelude default is what the
    proof should use (the branch files set [Default Proof Using "W"] inside
    their sections; that setting does not cross a [Require]). *)
Set Default Proof Using "Type".

  (** The top-level dispatch: the one triple in [STEP], and **the one place in
      this development where ghost state is updated**.  Each branch lemma
      hands back a pure [step] witness together with the list of messages it
      consumed; here that becomes a single [own_raft_ghost_step].

      [iApply wp_fupd] up front is what makes that possible: the ghost update
      has to happen after the branch lemma returns, when the goal would
      otherwise be the bare postcondition with no fancy update to absorb. *)
  Lemma wp_raft__Step : wp_raft__Step_body.
  Proof.
    intros_ambient.
    intros cfg γ r id s m.
    (* Not [subst cfg]: the branch lemmas below are applied to [cfg] by
       name, and with the binder gone that resolves to Perennial's global
       [cfg] (a [language → Type]).  Move the witness instead. *)
    intros Hcfg.
    intros Helection Hin Hhup Hvote Hvoteresp.
    iIntros (Φ) "(#Hinit & Hphys & Hghost & #Hm & #Hctx) HΦ".
    iApply wp_fupd.
    destruct Helection as [Hty | [Hty | Hty]].
    - (* MsgHup: a local message, handled by [hup]. *)
      destruct (Hhup Hty) as [Hmterm Hnowrap].
      wp_apply (H.wp_Step_MsgHup cfg with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hst & %Herr)".
      assert (step γ.(re_cfg) id s [] s') as Hst' by (rewrite Hcfg; exact Hst).
      iMod (own_raft_ghost_step_0 _ _ _ _ Hst' with "Hghost") as "Hghost".
      iModIntro. iApply ("HΦ" $! err s'). iFrame.
      iPureIntro. split; [by eexists []|done].
    - (* MsgVote: answer the vote request, stepping down first if needed. *)
      destruct (Hvote Hty) as (Hto & Hterm & Hfnz).
      iDestruct ("Hm" $! mtype.Vote with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVote. }
      wp_apply (V.wp_Step_MsgVote cfg with "[$Hphys $Hctx]"); [done..|].
      iIntros (err s') "(Hphys & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      assert (step γ.(re_cfg) id s recv s') as Hstep'
        by (rewrite Hcfg; exact Hstep).
      iMod (own_raft_ghost_step _ _ _ _ _ Hstep' with "[] Hghost") as "Hghost".
      { iApply big_sepL_intro. iIntros "!> %k %m' %Hk".
        rewrite (Hrecv m'); [iFrame "#"|by eapply list_elem_of_lookup_2]. }
      iModIntro. iApply ("HΦ" $! err s'). iFrame.
      iPureIntro. split; [by eexists recv|done].
    - (* MsgVoteResp: tally the vote, possibly winning or losing. *)
      destruct (Hvoteresp Hty) as [Hto Hterm].
      iDestruct ("Hm" $! mtype.VoteResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVoteResp. }
      wp_apply (R.wp_Step_MsgVoteResp cfg with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      assert (step γ.(re_cfg) id s recv s') as Hstep'
        by (rewrite Hcfg; exact Hstep).
      iMod (own_raft_ghost_step _ _ _ _ _ Hstep' with "[] Hghost") as "Hghost".
      { iApply big_sepL_intro. iIntros "!> %k %m' %Hk".
        rewrite (Hrecv m'); [iFrame "#"|by eapply list_elem_of_lookup_2]. }
      iModIntro. iApply ("HΦ" $! err s'). iFrame.
      iPureIntro. split; [by eexists recv|done].
  Qed.

End StepProof.
