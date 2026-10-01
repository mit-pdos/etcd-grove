Require Export New.proof.go_etcd_io.raft.election_proof.postulates_matchAckIndexer__AckedIndex.

Module MatchAckIndexerAckedIndexProof (P : MATCHACKINDEXER__ACKEDINDEX_POSTULATES)
  : MATCHACKINDEXER__ACKEDINDEX.

  (** [prs] and [pvs] have the same domain ([big_sepM2]), so the lookup
      hits exactly when [pvs_acked pvs id] is [Some]. *)
  Lemma wp_matchAckIndexer__AckedIndex : wp_matchAckIndexer__AckedIndex_body.
  Proof.
    intros_ambient.
    intros mref prs pvs id.
    wp_start as "Hm". iNamed "Hm".
    wp_auto.
    wp_apply (wp_map_lookup2 with "Hprs") as "_".
    iDestruct (big_sepM2_lookup_iff with "Hprogs") as %Hiff.
    rewrite /pvs_acked.
    destruct (prs !! id) as [pr|] eqn:Hpr.
    - destruct (proj1 (Hiff id) ltac:(by eexists)) as [[pv iv] Hpv].
      rewrite Hpv /=.
      iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hpr Hpv with "Hprogs")
        as "[Hp Hback]".
      iNamed "Hp". simpl.
      wp_auto.
      iDestruct ("Hback" with "[Hpv Hinfl]") as "Hprogs".
      { rewrite /own_progress. iFrame "∗%". }
      iApply "HΦ". iFrame "∗#".
    - assert (pvs !! id = None) as ->.
      { destruct (pvs !! id) eqn:Hv; last done.
        exfalso. destruct (proj2 (Hiff id) ltac:(by eexists)) as [? Hc].
        congruence. }
      simpl. wp_auto.
      iApply "HΦ". iFrame "∗#".
  Qed.

End MatchAckIndexerAckedIndexProof.
