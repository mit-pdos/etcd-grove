Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_slices.

Module CampaignProof (P : CAMPAIGN_POSTULATES) : CAMPAIGN.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Lemma wp_campaign (r : loc) (id : w64) (s : nstate.t) (t : raft.CampaignType.t) :
  t ≠ campaignPreElection →
  s.(nstate.role) ≠ role.Leader →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "campaign" #t
  {{{ (peers : list w64), RET #();
      ⌜ peers ≡ₚ elements (cfg ∖ {[id]}) ⌝ ∗
      let s' := become_candidate id s in
      own_raft_phys cfg r id
        (send_msgs s'
           ([msg.mk mtype.VoteResp id id s'.(nstate.term) false] ++
            ((λ to, msg.mk mtype.Vote id to s'.(nstate.term) false) <$> peers))) }}}.
Proof.
  intros Ht Hrole Hid_cfg.
  wp_start as "Hphys". iNamed "Hphys". wp_auto.
  (* [promotable] is true, since [id ∈ cfg]; the warning is not logged. *)
  wp_apply (wp_raft__promotable with "[$Hr $Htrk $Hlog]")
    as "%b (Hr & Htrk & Hlog & %Hb)".
  assert (b = true) as ->.
  { rewrite Hb Hid. by apply bool_decide_eq_true_2. }
  wp_auto.
  (* not a pre-election, so [becomeCandidate] *)
  rewrite bool_decide_eq_false_2; last exact Ht.
  wp_auto.
  iAssert (own_raft_phys cfg r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
  { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
  wp_apply (P.wp_raft__becomeCandidate _ _ _ _ Hrole with "[$Hphys]") as "Hphys".
  iNamedSuffix "Hphys" "1". wp_auto.
  (* nonce 0 *) Show.
Admitted.

End helpers.

Set Default Proof Using "Type".

  Lemma wp_raft__campaign : wp_raft__campaign_body.
  Proof.
  Admitted.

End CampaignProof.
