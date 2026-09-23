Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__hup.

Module HupProof (P : HUP_POSTULATES) : HUP.
Import P.

  (** [hup] has three early returns and one real path, and the postcondition
      is disjunctive to match.  The three early returns leave the struct
      alone, so they hand back [s] itself and [step_refl]; the last path is
      [campaign], whose postcondition names the resulting state outright and
      whose [step] witness is [step_campaign].

      Two of the branches are decided rather than taken:

      - [r.state == StateLeader] is decided by [Hstate] together with
        injectivity of [state_w64] -- the [≠ W64 2] fact in the non-leader
        branch is the same computation [becomeCandidate] does for its panic
        check.
      - [r.hasUnappliedConfChanges()] returns [false] (no reconfiguration is
        in scope), so its logging arm is dead code.

      [promotable] is the one branch genuinely taken both ways: its result is
      [bool_decide (r.id ∈ cfg)], which is exactly the [id ∈ cfg] premise
      [campaign] needs, so the two arms are "campaign" and "return".  Note it
      wants the pieces of [own_raft_phys] ([r ↦ rv], [own_tracker],
      [own_raftLog]) rather than the sealed predicate, which is why the proof
      keeps it unpacked and re-seals only for the [campaign] call. *)
  Lemma wp_raft__hup : wp_raft__hup_body.
  Proof.
    intros_ambient.
    intros cfg r id s t.
    intros Ht Hnowrap Hwf.
    pose proof Hwf as [Hstepfn_wf Hlent].
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    destruct (decide (s.(nstate.role) = role.Leader)) as [Hrl|Hrl].
    - (* already a leader: log and return, having done nothing *)
      rewrite Hstate Hrl bool_decide_eq_true_2 //. wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { rewrite /log_methods. set_solver. }
      iApply ("HΦ" $! s).
      iSplitL "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
      { iApply (own_raft_phys_intro with "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      iPureIntro. split; [done | apply step_refl].
    - (* not a leader *)
      assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
      { destruct (s.(nstate.role)) eqn:Hro; try congruence;
          rewrite /state_w64 /StateFollower /StateCandidate;
          intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq;
          discriminate. }
      rewrite Hstate bool_decide_eq_false_2 //.
      iAssert (own_raft_phys cfg r id s)
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
        as "Hphys".
      { iApply (own_raft_phys_intro with "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      wp_auto.
      wp_apply (wp_raft__promotable _ _ _ _ Hlent with "[$Hphys]")
        as "%b [Hphys %Hb]".
      destruct b.
      + (* a voter, so it may campaign *)
        wp_auto.
        wp_apply (wp_raft__hasUnappliedConfChanges _ _ _ _ Hlent with "[$Hphys]")
          as "Hphys".
        assert (id ∈ cfg) as Hin.
        { symmetry in Hb. by apply bool_decide_eq_true_1 in Hb. }
        iClear "Hlogger".
        iNamedSuffix "Hphys" "1".
        wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
        wp_auto. rewrite Hlok1.
        wp_apply (wp_Logger__logf with "Hlogger1").
        { rewrite /log_methods. set_solver. }
        iAssert (own_raft_phys cfg r id s)
          with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
          as "Hphys".
        { iApply (own_raft_phys_intro with
            "Hr1 Hlogger1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
            done. }
        wp_apply (P.wp_raft__campaign _ _ _ _ _ Ht Hrl Hin Hnowrap Hlent
                    with "[$Hphys]")
          as "%peers [%Hpeers Hphys]".
        iApply "HΦ". iFrame "Hphys".
        iPureIntro. split; first by apply nstate_wf_send_msgs, nstate_wf_become_candidate.
        rewrite to_pstate_send_msgs to_pstate_become_candidate.
        apply step_campaign; done.
      + (* unpromotable: log and return, having done nothing *)
        iClear "Hlogger".
        iNamedSuffix "Hphys" "1".
        wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
        wp_auto. rewrite Hlok1.
        wp_apply (wp_Logger__logf with "Hlogger1").
        { rewrite /log_methods. set_solver. }
        iApply ("HΦ" $! s).
        iSplitL "Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1".
        { iApply (own_raft_phys_intro with
            "Hr1 Hlogger1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
            done. }
        iPureIntro. split; [done | apply step_refl].
  Qed.

End HupProof.
