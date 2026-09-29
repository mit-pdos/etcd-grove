Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.

Module BecomeFollowerProof (P : BECOMEFOLLOWER_POSTULATES) : BECOMEFOLLOWER.
Import P.

  Lemma wp_raft__becomeFollower : wp_raft__becomeFollower_body.
  Proof.
    intros_ambient.
    intros cfg r id s term lead.
    wp_start as "Hphys". wp_auto.
    (* [r.step := stepFollower] *)
    wp_apply (wp_raft_store_step with "Hphys") as "Hphys".
    (* [reset]'s state is left to the frame: given explicitly, it has to be
       matched against [Hphys] up to conversion, which ran for 24 minutes
       before failing (2026-09-22) *)
    wp_apply (P.wp_raft__reset with "[$Hphys]").
    iIntros (pvs) "Hphys".
    (* [r.tick], [r.lead := lead], [r.state := StateFollower] *)
    wp_auto. (wp_apply (wp_raft_store_tick with "Hphys") as "Hphys"; wp_apply (wp_raft_store_lead with "Hphys") as "Hphys"; wp_apply (wp_raft_store_state _ _ _ _ role.Follower with "Hphys") as "Hphys").
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    wp_apply wp_traceBecomeFollower. try wp_auto.
    iApply ("HΦ" $! pvs).
    (* the stores above, in the order the Go code makes them, give
       [become_follower] up to the order of the record updates; do not
       [simpl] here -- the state carries [functions raft.stepFollower []],
       and [simpl] goes into the semantics tables (12+ minutes, 2026-09-22) *)
    iApply (own_raft_phys_eq with "Hphys"). by destruct s.
  Qed.

End BecomeFollowerProof.
