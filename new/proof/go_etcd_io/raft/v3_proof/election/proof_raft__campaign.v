Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_slices.

Module CampaignProof (P : CAMPAIGN_POSTULATES) : CAMPAIGN.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Lemma wp_map_len_uint64 (mref : loc) dq (m : gmap w64 unit) :
  {{{ mref ↦${dq} m }}}
    #(functions go.len [go.MapType go.uint64 (go.StructType [])]) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  destruct (go.is_map_domain_exists _ _ His_map) as [ks Hks].
  pose proof (go.internal_map_length_step_pure mv ks Hks) as Hlenstep.
  wp_auto.
  (* [length ks = size m]: the same argument [wp_map_for_range] makes. *)
  assert (length ks = size m) as ->.
  { eapply go.is_map_domain_pure in Hks; last exact His_map.
    destruct Hks as [Hnodup Hiff].
    assert (Forall (λ kv, ∃ (k : w64), kv = #k) ks) as Heq.
    { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
      intros Hk. apply Hdom. by apply Hiff. }
    apply Forall_exists_Forall2_l in Heq as [keys Heq].
    apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
    rewrite list_fmap_id in Heq. subst.
    assert (list_to_set keys = dom m) as Hl.
    { rewrite sets.set_eq. intros k. rewrite elem_of_list_to_set.
      specialize (Hiff #k). specialize (Hagree k).
      rewrite list_elem_of_fmap_inj in Hiff.
      rewrite -Hiff Hagree elem_of_dom. by destruct lookup. }
    apply NoDup_fmap in Hnodup; last tc_solve.
    rewrite length_fmap.
    rewrite <- (size_list_to_set (C:=gset w64)); last done.
    rewrite Hl size_dom //. }
  iApply "HΦ". iFrame "∗%".
Qed.

Lemma own_raft_phys_outbox_perm (r : loc) (id : w64) (s : nstate.t)
    (o1 o2 : list msg.t) :
  o1 ≡ₚ o2 →
  own_raft_phys cfg r id (s <| nstate.outbox := o1 |>) -∗
  own_raft_phys cfg r id (s <| nstate.outbox := o2 |>).
Proof.
  intros Hperm. rewrite /own_raft_phys. iIntros "H". iNamed "H".
  iExists rv, msgs, msgsAA, lok. simpl in *. iFrame "∗#%".
  iPureIntro. by rewrite -Hperm.
Qed.

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
  (* Two facts this proof needs that nothing in scope supplies; see the note
     at the end of the file.  The [admit] below is the *only* gap. *)
  destruct (decide (Z.of_nat (size cfg) < 2 ^ 63 ∧
                    word.add s.(nstate.term) (W64 1) ≠ W64 0))
    as [[Hcfg_fits Hno_wrap] | Hout_of_scope]; last first.
  { (* NOT PROVABLE from this spec -- see "Two missing scope assumptions". *)
    admit. }
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
  (* the voter ids, as a map.  [IDs] wants the tracker's location, which the
     generated [AccessStrict] instance splits out of [r ↦ rv0]; pin the load
     instance, since the call does not change the tracker value. *)
  iDestruct (access_strict
               (A := r.[raft.raft.t, "trk"] ↦ rv0.(raft.raft.trk'))
               (A' := r.[raft.raft.t, "trk"] ↦ rv0.(raft.raft.trk'))
               (P := r ↦ rv0) (P' := r ↦ rv0)
               with "Hr1") as "[Htrkf Hrback]".
  wp_apply (wp_campaign_peer_ids with "[$Htrkf $Htrk1]")
    as "%mref %idm (Htrkf & Htrk1 & Hidm & %Hdomidm)".
  iDestruct ("Hrback" with "Htrkf") as "Hr1".
  wp_apply (wp_map_len_uint64 with "Hidm") as "Hidm".
  assert (size idm = size cfg) as Hszidm.
  { rewrite -Hdomidm size_dom //. }
  rewrite Hszidm.
  wp_apply (wp_slice_make3 (V:=w64) (t:=go.uint64))
    as (sl) "(Hsl & Hsl_cap & %Hslcap)"; first word.
  replace (sint.nat (W64 0)) with 0%nat by done. simpl.
  (* The map range appends the voter ids to [ids], in the order [IDs] yields
     them.  [0 ≤ i] has to be part of the invariant: [wp_map_for_range]'s
     body hypothesis is quantified over all [i] whose lookup succeeds, and
     without it [take (Z.to_nat (i+1))] cannot be split. *)
  set (Pmap := (λ (keys : list w64) (i : Z),
    ∃ (sl' : slice.t) (x : w64),
      "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
      "ids" ∷ ids_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* take (Z.to_nat i) keys ∗
      "Hsl_cap" ∷ own_slice_cap w64 sl' (DfracOwn 1) ∗
      "id" ∷ id_ptr ↦ x)%I).
  wp_apply (wp_map_for_range Pmap with "Hidm").
  iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
  iSplitL "ids Hsl Hsl_cap id".
  { rewrite /Pmap. iExists sl, (W64 0). rewrite take_0. iFrame.
    iPureIntro. lia. }
  iSplitL "".
  { iIntros "!>" (i key vv) "[%Hkey %Hvv] HP". rewrite /Pmap. iNamed "HP".
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl2 [Hsl2 _]".
    wp_auto.
    replace (sint.nat (W64 0)) with 0%nat by done.
    rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
    wp_apply (wp_slice_append with "[$Hsl $Hsl_cap $Hsl2]")
      as "%sl3 (Hsl & Hsl_cap & _)".
    (* nonce 73334785 *) Show.
    admit. }
  admit.
Admitted.

End helpers.

Set Default Proof Using "Type".

  Lemma wp_raft__campaign : wp_raft__campaign_body.
  Proof.
  Admitted.

End CampaignProof.
