Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeCandidate.

Module BecomeCandidateProof (P : BECOMECANDIDATE_POSTULATES) : BECOMECANDIDATE.
Import P.

  Lemma wp_raft__becomeCandidate : wp_raft__becomeCandidate_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    intros Hrole. wp_start as "Hphys". wp_auto.
    (* [becomeCandidate] panics on a leader; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateFollower /StateCandidate;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
    rewrite bool_decide_eq_false_2 //. wp_auto.
    (* [r.step := stepCandidate], then [reset] at [r.Term + 1] *)
    (wp_apply (wp_raft_store_step with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys").
    (* [reset]'s state is left to the frame: given explicitly, it has to be
       matched against [Hphys] up to conversion, which ran for 24 minutes
       before failing (2026-09-22) *)
    wp_apply (P.wp_raft__reset with "[$Hphys]").
    iIntros (pvs) "Hphys".
    (* [r.tick], [r.Vote := r.id], [r.state := StateCandidate] *)
    wp_auto. (wp_apply (wp_raft_store_tick with "Hphys") as "Hphys"; wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_store_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_store_state _ _ _ _ role.Candidate with "Hphys") as "Hphys").
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    wp_apply wp_traceBecomeCandidate. try wp_auto.
    iApply ("HΦ" $! pvs).
    (* the stores above give [become_candidate] up to the order of the record
       updates; no [simpl]: the state carries a [functions …] value *)
    iApply (own_raft_phys_eq with "Hphys"). by destruct s.
  Qed.

End BecomeCandidateProof.
