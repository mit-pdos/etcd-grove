Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastHeartbeat.

Module RaftBcastHeartbeatProof (P : RAFT__BCASTHEARTBEAT_POSTULATES)
  : RAFT__BCASTHEARTBEAT.
Import P.

  (** [r.readOnly] through [own_raft_phys_readOnly], [heartbeatCtx] on the
      object it hands out, the object back unchanged; then
      [bcastHeartbeatWithCtx] with the [nil] context. *)
  Lemma wp_raft__bcastHeartbeat : wp_raft__bcastHeartbeat_body.
  Proof.
    intros_ambient.
    intros cfg r id s Hlead.
    wp_start as "Hphys". iNamed "Hphys".
    iDestruct (own_raft_phys_readOnly with "Hphys") as (ro) "(Hrof & Hro & Hback)".
    wp_auto.
    wp_apply (wp_readOnly__heartbeatCtx with "[$Hro]") as "Hro".
    iDestruct ("Hback" with "Hrof Hro") as "Hphys".
    wp_apply (wp_raft__bcastHeartbeatWithCtx _ _ _ _ _ Hlead with "[$Hphys]")
      as "%ms %pvs (Hphys & %Hms & %Hmm)".
    iApply "HΦ". iFrame "Hphys". done.
  Qed.

End RaftBcastHeartbeatProof.
