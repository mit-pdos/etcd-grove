Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__hup.

Module HupProof (P : HUP_POSTULATES) : HUP.
Import P.

  (** [hup] has three early returns and one real path, and the postcondition
      is disjunctive to match.  The three early returns leave the struct
      alone, so they hand back [s] itself and [step_refl]; the last path is
      [campaign], whose postcondition names the resulting state outright and
      whose [step] witness is [step_campaign].

      Two of the branches are decided rather than taken:

      - [r.state == StateLeader] is decided by the loaded
        [state_w64 s.(nstate.role)] together with injectivity of
        [state_w64] -- the [≠ W64 2] fact in the non-leader branch is the
        same computation [becomeCandidate] does for its panic check.
      - [r.hasUnappliedConfChanges()] returns [false] (no reconfiguration is
        in scope), so its logging arm is dead code.

      [promotable] is the one branch genuinely taken both ways: its result is
      [bool_decide (r.id ∈ cfg)], which is exactly the [id ∈ cfg] premise
      [campaign] needs, so the two arms are "campaign" and "return". *)
  Lemma wp_raft__hup : wp_raft__hup_body.
  Proof.
    intros_ambient.
    intros cfg r id s t.
    intros Ht Hnowrap Hwf.
    pose proof Hwf as [Hstepfn_wf Hlent].
    wp_start as "Hphys". wp_auto.
    wp_raft_field.
    destruct (decide (s.(nstate.role) = role.Leader)) as [Hrl|Hrl].
    - (* already a leader: log and return, having done nothing *)
      rewrite Hrl bool_decide_eq_true_2 //. wp_auto.
      wp_raft_log.
      iApply ("HΦ" $! s). iFrame "Hphys".
      iPureIntro. split; [done | apply step_refl].
    - (* not a leader *)
      assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
      { destruct (s.(nstate.role)) eqn:Hro; try congruence;
          rewrite /state_w64 /StateFollower /StateCandidate;
          intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq;
          discriminate. }
      rewrite bool_decide_eq_false_2 //.
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
        wp_raft_log.
        wp_apply (P.wp_raft__campaign _ _ _ _ _ Ht Hrl Hin Hnowrap Hlent
                    with "[$Hphys]")
          as "%peers [%Hpeers Hphys]".
        iApply "HΦ". iFrame "Hphys".
        iPureIntro. split; first by apply nstate_wf_send_msgs, nstate_wf_become_candidate.
        rewrite to_pstate_send_msgs to_pstate_become_candidate.
        apply step_campaign; done.
      + (* unpromotable: log and return, having done nothing *)
        wp_auto.
        wp_raft_log.
        iApply ("HΦ" $! s). iFrame "Hphys".
        iPureIntro. split; [done | apply step_refl].
  Qed.

End HupProof.
