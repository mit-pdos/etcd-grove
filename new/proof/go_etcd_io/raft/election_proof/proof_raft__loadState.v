Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__loadState.

Module LoadStateProof (P : RAFT__LOADSTATE_POSTULATES) : RAFT__LOADSTATE.
Import P.

  Lemma wp_raft__loadState : wp_raft__loadState_body.
  Proof.
    intros_ambient.
    intros cfg r id s hs Hc.
    destruct (s.(nstate.logst)) as [prev sents uents lcm lap snap] eqn:Hls.
    cbn in Hc.
    wp_start as "Hphys".
    wp_auto.
    (* Each [r.raftLog.f] loads the pointer through the struct first, so the
       log is taken out ([own_raft_phys_log_at]) and put back around each
       use; the first two put it back unchanged. *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_at with "Hphys") as "[HL Hlogback]".
    iEval (rewrite Hls) in "HL".
    iDestruct (own_raftLog_nowrap with "HL") as "[%Hnw HL]".
    cbn in Hnw.
    assert (uint.Z (log_last (logstate.mk prev sents uents lcm lap snap))
            = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
              + Z.of_nat (length uents))%Z as Hll.
    { rewrite /log_last /=.
      pose proof (word.unsigned_range prev.(raft.entryID.index')).
      rewrite word.unsigned_of_Z_nowrap; lia. }
    rewrite Hll in Hc.
    iDestruct (own_raftLog_struct with "HL") as (lv) "(Hl & [%Hcm %Hap] & HLback)".
    logstate_simpl.
    wp_auto.
    iDestruct ("HLback" with "Hl") as "HL".
    iDestruct ("Hlogback" with "HL") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys".
    { destruct s; simpl in Hls; subst. done. }
    rewrite bool_decide_eq_false_2; last (subst; word). try wp_auto.
    (* [r.raftLog.lastIndex()] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_at with "Hphys") as "[HL Hlogback]".
    iEval (rewrite Hls) in "HL".
    wp_apply (P.wp_raftLog__lastIndex with "[$HL]") as "%li [HL %Hli]".
    logstate_simpl.
    iDestruct ("Hlogback" with "HL") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys".
    { destruct s; simpl in Hls; subst. done. }
    rewrite bool_decide_eq_false_2; last word.
    try wp_auto.
    (* [r.raftLog.committed = state.Commit] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_at with "Hphys") as "[HL Hlogback]".
    iEval (rewrite Hls) in "HL".
    iDestruct (own_raftLog_unfold with "HL") as (lv2) "(Hl & %Hcm2 & %Hap2 & Hcore)".
    logstate_simpl.
    try wp_auto.
    set ls' := logstate.mk prev sents uents hs.(raftpb.HardState.Commit') lap snap.
    iAssert (own_raftLog s.(nstate.log) ls')%I with "[Hl Hcore]" as "HL".
    { iEval (rewrite /own_raftLog_core /=) in "Hcore".
      iDestruct "Hcore" as (sprev stored) "Hcore". iNamed "Hcore".
      reseal_raftLog.
      all: simpl; subst; rewrite ?Hcm2 in Happlied; lia. }
    iDestruct ("Hlogback" with "HL") as "Hphys".
    wp_apply (wp_raft_store_Term with "Hphys") as "Hphys".
    try wp_auto.
    wp_apply (wp_raft_store_Vote with "Hphys") as "Hphys".
    try wp_auto.
    iApply "HΦ".
    iApply (own_raft_phys_eq with "Hphys").
    by destruct s.
  Qed.

End LoadStateProof.
