Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastHeartbeatWithCtx.

Module RaftBcastHeartbeatWithCtxProof (P : RAFT__BCASTHEARTBEATWITHCTX_POSTULATES)
  : RAFT__BCASTHEARTBEATWITHCTX.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** The heartbeat [sendHeartbeat] sends is [heartbeat_ok] at the protocol
    reading of a leader's state, given its two bounds against that state's
    [committed] and [Match]. *)
Local Lemma heartbeat_ok_intro id (s : nstate.t) (to c : w64) :
  s.(nstate.role) = prole.Leader →
  to ≠ id →
  uint.Z c ≤ uint.Z s.(nstate.logst).(logstate.committed) →
  uint.Z c ≤ uint.Z (default (W64 0) (prvals_match s.(nstate.prvals) !! to)) →
  heartbeat_ok id (to_pstate s)
    (msg.mk mtype.Heartbeat id to s.(nstate.term) false (W64 0) (W64 0) c (W64 0) []).
Proof.
  intros Hl Hto Hc Hm. rewrite /heartbeat_ok /match_of /to_pstate /=.
  rewrite decide_True //; split_and?; done.
Qed.

(** ** [bcastHeartbeatWithCtx]

    The same proof as [bcastAppend]'s ([proof_raft__bcastAppend.v]): the
    caller invariant of [Visit] is the raft struct with a tracker-shaped
    hole (the wand of [own_raft_phys_tracker_prvals]), quantified over the
    [Progress] values; [ms] accumulates.  The difference is the fact
    accumulated: each heartbeat is [heartbeat_ok] at [to_pstate s].  The
    closure's [sendHeartbeat] is called at [send_msgs s ms <| prvals :=
    pvsx |>], whose [committed] is [s]'s and whose [Match] values are
    [s]'s (the invariant's [Hmm]), so its bounds are bounds at [s]. *)
Lemma wp_bcast_hb (r : loc) (id : w64) (s : nstate.t) (ctx : slice.t) :
  s.(nstate.role) = prole.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastHeartbeatWithCtx" #ctx
  {{{ (ms : list msg.t) pvs, RET #();
      own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
      ⌜ Forall (heartbeat_ok id (to_pstate s)) ms ⌝ ∗
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.
Proof.
  intros Hlead.
  wp_start as "Hphys". wp_auto.
  iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
  iDestruct (own_raft_phys_tracker_prvals with "Hphys")
    as (tv) "(Htrkf & Htrk & Hrest)".
  wp_apply (wp_ProgressTracker__Visit _ _ _ (trk.mk s.(nstate.votes) s.(nstate.progress) _) _
              (λ _ pvsx, ∃ (ms : list msg.t),
                 "rp" ∷ r_ptr ↦ r ∗
                 "cp" ∷ ctx_ptr ↦ ctx ∗
                 "%Hms" ∷ ⌜ Forall (heartbeat_ok id (to_pstate s)) ms ⌝ ∗
                 "%Hmm" ∷ ⌜ prvals_match pvsx = prvals_match s.(nstate.prvals) ⌝ ∗
                 "Hrest" ∷ (∀ tvx pvsx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                          own_tracker cfg tvx (trk.mk s.(nstate.votes) s.(nstate.progress) pvsx) -∗
                          own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvsx |>)))%I
              with "[$Htrkf $Htrk r ctx Hrest]").
  { iSplitL "r ctx Hrest".
    { iExists []. iFrame "r ctx". iSplitR; first (iPureIntro; by apply Forall_nil).
      iSplitR; first done.
      iIntros (tvx pvsx) "Hf Ht". iDestruct ("Hrest" with "Hf Ht") as "Hphys".
      iApply (own_raft_phys_eq with "Hphys"). reflexivity. }
    (* the closure *)
    iModIntro. iIntros (i pr tv0 pvs0 p D).
    wp_start as "(%Hicfg & %Hpri & %Hpvi & %HmaxI & Htrkf & Hpr & Hback & HI)".
    iNamed "HI".
    iDestruct ("Hback" with "Hpr") as "Htrk".
    iDestruct ("Hrest" with "Htrkf Htrk") as "Hphys".
    wp_auto. wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    destruct (decide (i = id)) as [Hii|Hii].
    - (* the leader itself: nothing is sent *)
      rewrite bool_decide_eq_true_2 //. wp_auto.
      iDestruct (own_raft_phys_tracker_prvals with "Hphys")
        as (tv1) "(Htrkf & Htrk & Hrest)".
      iApply "HΦ". iExists tv1, _. iFrame "Htrkf Htrk".
      iExists ms. iFrame "rp cp". iSplitR; first done.
      iSplitR; first (iPureIntro; simpl; rewrite (insert_id _ _ _ Hpvi) //).
      iIntros (tvx pvsx) "Hf Ht". iDestruct ("Hrest" with "Hf Ht") as "Hphys".
      iApply (own_raft_phys_eq with "Hphys"). reflexivity.
    - (* a peer: one heartbeat *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft__sendHeartbeat _ _ _ _ i ctx Hii Hicfg with "[$Hphys]")
        as "%c %pvs' (Hphys & %Hc1 & %Hc2 & %Hmm')".
      try wp_auto.
      iDestruct (own_raft_phys_tracker_prvals with "Hphys")
        as (tv1) "(Htrkf & Htrk & Hrest)".
      iApply "HΦ". iExists tv1, _. iFrame "Htrkf Htrk".
      iExists (ms ++ [msg.mk mtype.Heartbeat id i s.(nstate.term) false
                        (W64 0) (W64 0) c (W64 0) []]).
      iFrame "rp cp".
      iSplitR.
      { iPureIntro. apply Forall_app_2; [ exact Hms | ].
        apply Forall_singleton. apply heartbeat_ok_intro; [done|done| |].
        - exact Hc1.
        - simpl in Hc2. rewrite (insert_id _ _ _ Hpvi) Hmm in Hc2. exact Hc2. }
      iSplitR.
      { iPureIntro. simpl. rewrite Hmm' /= (insert_id _ _ _ Hpvi) //. }
      iIntros (tvx pvsx) "Hf Ht". iDestruct ("Hrest" with "Hf Ht") as "Hphys".
      iApply (own_raft_phys_eq with "Hphys").
      rewrite /send_msgs -assoc. reflexivity. }
  iIntros "H". iDestruct "H" as (tvfin pvsfin) "(Htrkf & Htrk & HI)".
  iNamed "HI".
  iDestruct ("Hrest" $! tvfin pvsfin with "Htrkf Htrk") as "Hphys".
  wp_auto.
  iApply ("HΦ" $! ms pvsfin). iFrame "Hphys %".
Qed.

End helpers.

Set Default Proof Using "Type".

  Lemma wp_raft__bcastHeartbeatWithCtx : wp_raft__bcastHeartbeatWithCtx_body.
  Proof.
    intros_ambient.
    intros cfg r id s ctx Hlead.
    by apply wp_bcast_hb.
  Qed.

End RaftBcastHeartbeatWithCtxProof.
