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

(** [own_raft_phys] constrains the outbox only up to permutation (that is the
    whole point of the [≡ₚ] in [Houtbox]), so a state may be replaced by any
    other that agrees on the five scalar fields and permutes the outbox.
    [campaign] needs this twice: to see [s'] as [send_msgs s' []] when the
    send loop starts, and to reorder the messages the loop actually sent into
    the order the spec names. *)
Lemma own_raft_phys_outbox (r : loc) (id : w64) (s1 s2 : nstate.t) :
  s1.(nstate.term) = s2.(nstate.term) →
  s1.(nstate.vote) = s2.(nstate.vote) →
  s1.(nstate.lead) = s2.(nstate.lead) →
  s1.(nstate.role) = s2.(nstate.role) →
  s1.(nstate.votes) = s2.(nstate.votes) →
  s1.(nstate.outbox) ≡ₚ s2.(nstate.outbox) →
  own_raft_phys cfg r id s1 -∗ own_raft_phys cfg r id s2.
Proof.
  intros H1 H2 H3 H4 H5 H6. rewrite /own_raft_phys.
  iIntros "H". iNamed "H". iExists rv, msgs, msgsAA, lok.
  rewrite -H5.
  iFrame "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Hlogger".
  iPureIntro. split_and!; first [ done | congruence | by rewrite -H6 ].
Qed.

(** Two sends in a row grow the outbox by the concatenation. *)
Lemma send_msgs_app (s0 : nstate.t) (ms1 ms2 : list msg.t) :
  send_msgs (send_msgs s0 ms1) ms2 = send_msgs s0 (ms1 ++ ms2).
Proof. rewrite /send_msgs /= app_assoc //. Qed.

Lemma own_raft_phys_send_nil (r : loc) (id : w64) (s0 : nstate.t) :
  own_raft_phys cfg r id s0 -∗ own_raft_phys cfg r id (send_msgs s0 []).
Proof.
  iIntros "H". iApply (own_raft_phys_outbox with "H"); try done.
  rewrite /send_msgs /= app_nil_r //.
Qed.

Lemma own_raft_phys_send_perm (r : loc) (id : w64) (s0 : nstate.t)
    (ms1 ms2 : list msg.t) :
  ms1 ≡ₚ ms2 →
  own_raft_phys cfg r id (send_msgs s0 ms1) -∗
  own_raft_phys cfg r id (send_msgs s0 ms2).
Proof.
  iIntros (Hperm) "H". iApply (own_raft_phys_outbox with "H"); try done.
  rewrite /send_msgs /=. by apply Permutation_app_head.
Qed.

(** Three one-liners that exist only so that [set_solver] runs in a small
    context.  Inside [wp_campaign] the local context is ~60 hypotheses wide
    and [set_solver]'s [naive_solver] takes minutes on it. *)
Lemma gset_split (X : gset w64) (z : w64) : z ∈ X → {[z]} ∪ (X ∖ {[z]}) = X.
Proof.
  intros Hz. rewrite sets.set_eq. intros w.
  rewrite elem_of_union elem_of_difference elem_of_singleton.
  destruct (decide (w = z)) as [->|Hne]; naive_solver.
Qed.

Lemma not_elem_of_diff_singleton (X : gset w64) (z : w64) : z ∉ X ∖ {[z]}.
Proof. rewrite elem_of_difference elem_of_singleton. naive_solver. Qed.

Lemma elem_of_elements_1 (X : gset w64) (z : w64) : z ∈ elements X → z ∈ X.
Proof. intros Hz. by apply elem_of_elements in Hz. Qed.

Lemma elements_split (X : gset w64) (z : w64) :
  z ∈ X → elements X ≡ₚ z :: elements (X ∖ {[z]}).
Proof.
  intros Hz. rewrite -{1}(gset_split X z Hz).
  apply elements_union_singleton, not_elem_of_diff_singleton.
Qed.

Lemma Infof_is_log_method : "Infof"%go ∈ log_methods.
Proof. rewrite /log_methods list_elem_of_In /=. right. by left. Qed.

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
  (* Two facts this proof needs that nothing in scope supplies; see
     "Where this got to" at the end of the file. *)
  destruct (decide (Z.of_nat (size cfg) < 2 ^ 63 ∧
                    word.add s.(nstate.term) (W64 1) ≠ W64 0))
    as [[Hcfg_fits Hno_wrap] | Hout_of_scope]; last first.
  { (* NOT PROVABLE from this spec; see the note at the end of the file. *)
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
    iRight. iLeft. iSplitR; first done.
    assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc.
    { exact (Z2Nat.inj_succ i Hi). }
    assert (take (Z.to_nat (i + 1)) keys = take (Z.to_nat i) keys ++ [key])
      as Htake.
    { rewrite Hsucc. by apply take_S_r. }
    iExists sl3, key. rewrite Htake. iFrame. iPureIntro.
    change (0 <= i + 1)%Z. lia. }
  (* the range is over, so [ids] holds every voter id exactly once *)
  iIntros "HP". rewrite /Pmap. iNamed "HP".
  rewrite Nat2Z.id -Hklen firstn_all.
  assert (keys ≡ₚ elements cfg) as Hkeys_perm.
  { rewrite -Hdomidm -Hkset. by rewrite elements_list_to_set. }
  wp_auto.
  wp_apply (wp_slices_Sort with "[$Hsl]") as "%xs (Hsl & %Hxs)".
  (* re-seal for the send loop; [send] wants the whole struct *)
  iAssert (own_raft_phys cfg r id (become_candidate id s))
    with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
    as "Hphys".
  { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0. iFrame "∗#%". }
  iRename "id" into "idold".
  wp_alloc cur_ptr as "cur".
  wp_auto.
  (* [cmsg y] is the message [campaign] sends on behalf of voter [y]: the
     self-addressed [MsgVoteResp] when [y] is this node, a [MsgVote]
     otherwise.  [send] panics on a self-addressed non-response, which is
     exactly why the code splits these two cases. *)
  assert (length xs = size cfg) as Hlenxs.
  { rewrite -(Permutation_length Hxs) Hklen Hszidm //. }
  (* [wp_if_destruct] runs [subst], which would otherwise eliminate [cfg] and
     [id] through these two equations and rename them throughout. *)
  clear Hid Hid1 Hdomidm Hkset Hb.
  set (T := rv0.(raft.raft.Term')).
  assert (T = word.add s.(nstate.term) (W64 1)) as HTeq by exact Hterm1.
  assert (T ≠ W64 0) as HTnz by (rewrite HTeq; exact Hno_wrap).
  set (cmsg := (λ (y : w64), if decide (y = id)
                             then msg.mk mtype.VoteResp id id T false
                             else msg.mk mtype.Vote id y T false)).
  assert (cmsg id = msg.mk mtype.VoteResp id id T false) as Hcmsg_self.
  { rewrite /cmsg /=. rewrite decide_True //. }
  assert (∀ z, z ≠ id → cmsg z = msg.mk mtype.Vote id z T false) as Hcmsg_peer.
  { intros z Hz. rewrite /cmsg /=. rewrite decide_False //. }
  (* [xs] enumerates the voters, so it is [id] followed by the other voters
     in some order -- which is exactly the shape [step_campaign] asks for. *)
  assert (xs ≡ₚ id :: elements (cfg ∖ {[id]})) as Hxs_split.
  { rewrite -Hxs Hkeys_perm. by apply elements_split. }
  assert (cmsg <$> elements (cfg ∖ {[id]})
          = (λ to, msg.mk mtype.Vote id to T false) <$> elements (cfg ∖ {[id]}))
    as Hpeers.
  { apply list_fmap_ext. intros i z Hiz.
    apply Hcmsg_peer. intros ->.
    apply (not_elem_of_diff_singleton cfg id), elem_of_elements_1.
    by eapply list_elem_of_lookup_2. }
  iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
  iDestruct (own_slice_len with "Hsl") as "%Hxslen".
  iAssert (∃ (n : w64),
     "i" ∷ i_ptr ↦ n ∗
     "%Hn" ∷ ⌜ 0 ≤ sint.Z n ≤ Z.of_nat (length xs) ⌝ ∗
     "Hphys" ∷ own_raft_phys cfg r id
       (send_msgs (become_candidate id s)
          (cmsg <$> take (Z.to_nat (sint.Z n)) xs)))%I
    with "[i Hphys]" as "IH".
  { iExists (W64 0).
    rewrite (_ : Z.to_nat (sint.Z (W64 0)) = 0%nat); last word.
    rewrite take_0 /=. iFrame. iPureIntro.
    rewrite (_ : sint.Z (W64 0) = 0); last word. lia. }
  (* the bounds [word] needs to see that [i+1] does not overflow *)
  assert (sint.Z sl'.(slice.len) = Z.of_nat (length xs)) as Hsllen.
  { destruct Hxslen as [Hx1 Hx2]. rewrite Hx1 Z2Nat.id //. }
  assert (Z.of_nat (length xs) < 2 ^ 63) as Hxs63.
  { rewrite Hlenxs. exact Hcfg_fits. }
  wp_for "IH".
  wp_if_destruct.
  - (* one more voter to notify *)
    assert (∃ y, xs !! Z.to_nat (sint.Z n) = Some y) as [y Hy].
    { apply lookup_lt_is_Some_2. word. }
    rewrite decide_True; last word.
    wp_apply (wp_load_slice_index (V:=w64) (t:=go.uint64)
                sl' (sint.Z n) xs (DfracOwn 1) y with "[$Hsl]") as "Hsl";
      try first [ word | iPureIntro; exact Hy | tc_solve | done ].
    iNamedSuffix "Hphys" "2".
    assert (Z.to_nat (sint.Z (word.add n (W64 1))) = S (Z.to_nat (sint.Z n)))
      as Hsucc.
    { rewrite -Z2Nat.inj_succ; last word. f_equal. word. }
    assert (cmsg <$> take (Z.to_nat (sint.Z (word.add n (W64 1)))) xs
            = (cmsg <$> take (Z.to_nat (sint.Z n)) xs) ++ [cmsg y]) as Hgrow.
    { rewrite Hsucc (take_S_r _ _ y) // fmap_app //. }
    wp_auto.
    rewrite Hid2.
    destruct (decide (y = id)) as [->|Hney].
    + (* this node's own vote: a self-addressed [MsgVoteResp] *)
      rewrite bool_decide_eq_true_2 //. wp_auto.
      iAssert (own_raft_phys cfg r id
                 (send_msgs (become_candidate id s)
                    (cmsg <$> take (Z.to_nat (sint.Z n)) xs)))
        with "[Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2]"
        as "Hphys".
      { rewrite /own_raft_phys. iExists _, _, _, _. iFrame "∗#%". }
      (* STOPS HERE.  The rest of this branch is written but not yet
         checked; it is preserved verbatim in the comment at the end of the
         file, together with what went wrong last.  See "Where this got to". *)
      admit.
    + (* a peer: read the last entry, log, and send it a [MsgVote] -- also
         written but unchecked; see the comment at the end of the file. *)
      admit.
  - (* every voter has been notified -- the exit branch, also written but
       unchecked; see the comment at the end of the file. *)
    admit.
Admitted.

End helpers.

Set Default Proof Using "Type".

  Lemma wp_raft__campaign : wp_raft__campaign_body.
  Proof.
    intros_ambient.
    intros cfg r id s t.
    apply wp_campaign.
  Qed.


(** ** Where this got to, and the two scope assumptions the spec is missing

    [wp_campaign] is [Admitted].  Everything down to the body of the send
    loop is machine-checked; three things are not, and they are the three
    [admit]s:

    *** 1. The leading case split (unprovable as the spec stands)

    The proof opens with
    [destruct (decide (Z.of_nat (size cfg) < 2 ^ 63 ∧
                       word.add s.(nstate.term) (W64 1) ≠ W64 0))],
    and the negative branch is admitted because neither conjunct follows
    from anything in scope:

    - **The voter set must fit in a Go [int].**  [campaign] runs
      [ids := make([]uint64, 0, len(idMap))], and [make] panics on a
      negative capacity ([wp_slice_make3] requires
      [0 ≤ sint.Z len ≤ sint.Z cap]), while [len(idMap)] is
      [W64 (size cfg)].  Nothing bounds [size cfg]: [own_tracker] pins
      [dom prs = cfg] but says nothing about its size, and no amount of Iris
      ownership bounds the cardinality of a [gset w64] — [size cfg = 2 ^ 64]
      is consistent with every conjunct of [own_raft_phys].

    - **The term must not wrap.**  [becomeCandidate] raises the term to
      [word.add s.(nstate.term) (W64 1)], and [send] *panics* on a vote
      message whose term is zero ("term should be set when sending %s", see
      [raft__sendⁱᵐᵖˡ]) — which is exactly why [wp_raft__send_vote] requires
      [m.(raftpb.Message.Term') ≠ W64 0].  So as written the triple in
      [spec_raft__campaign.v] is **false**: at
      [s.(nstate.term) = 2 ^ 64 - 1] the Go code panics.

    Natural homes for these, neither of which could be made here: (1) a
    conjunct of [own_tracker] in [inv_tracker.v] — the Go progress map's
    length really is an [int] — or a hypothesis of
    [wp_raft__campaign_body]; (2) a conjunct of [own_raft_phys] in
    [inv_raft_phys.v] (say [uint.Z s.(nstate.term) + 1 < 2 ^ 64]), which
    every caller of [send] will want, or again a hypothesis of
    [wp_raft__campaign_body].

    *** 2 and 3. The send loop's two branches

    What *is* checked: the [promotable] warning (skipped, since [id ∈ cfg]
    makes it true), [becomeCandidate], [IDs] (through [access_strict] on the
    [trk] field), [make([]uint64, 0, len(idMap))] (via the new
    [wp_map_len_uint64] below — [golang/theory/map.v] has no [len] spec for
    maps, only the pure semantic step), the whole [map.for_range] that fills
    [ids], [slices.Sort], the send loop's setup and its [wp_for] invariant,
    the index load, and all the pure permutation bookkeeping
    ([Hxs_split], [Hpeers], [Hgrow], [Hsucc]).

    What is not: from the first [send] onwards.  The script below is the
    remaining work, verbatim, and it fails at the first
    [wp_apply P.wp_raft__send_vote] with

        iApply: cannot apply
        (▷ (own_raft_phys cfg r id (send_msgs … [msg.mk mtype.VoteResp id
             ?m.(raftpb.Message.To') ?m.(raftpb.Message.Term')
             ?m.(raftpb.Message.Reject')]) -∗ ?Goal (#())) -∗
         WP r @! (go.PointerType raft.raft) @! "send" (# ?m) {{ … }})

    i.e. the goal at that point is not yet the [send] call with a message
    *value*.  The likely cause is that [wp_auto] does not step through the
    [voteRespMsgType] call and the [raftpb.Message] composite literal that
    build [$a0]; [proof_voteRespMsgType.v] needs an explicit
    [rewrite /MsgVote bool_decide_eq_true_2] inside that function, so the
    call site probably needs the same.  Note also that [voteRespMsgType] is
    **not** in [CAMPAIGN_POSTULATES] even though [campaign] calls it — that
    is a second, smaller shared-file gap ([postulates_raft__campaign.v] and
    [link_raft__campaign.v] would need [Include VOTERESPMSGTYPE]).

    Two practical notes for whoever picks this up:

    - [set_solver] inside [wp_campaign] takes *minutes*: the local context is
      ~60 hypotheses wide and [naive_solver] chokes on it.  That is why
      [gset_split], [not_elem_of_diff_singleton], [elements_split],
      [elem_of_elements_1] and [Infof_is_log_method] are hoisted out as
      one-line lemmas.
    - [wp_if_destruct] runs [subst], which will eliminate [cfg] and [id]
      through [Hdomidm : dom idm = cfg] and [Hid : rv.(id') = id] and rename
      them throughout the rest of the proof; the [clear] before [wp_for] is
      there to stop that.

    *** The remaining script

      (* [wp_apply] discharges some of [send]'s five side conditions itself,
         so name them all and let each goal pick the one that fits. *)
      wp_apply (P.wp_raft__send_vote _ _ _ _ _ mtype.VoteResp with "[$Hphys]");
        try first [ done
                  | by right
                  | apply mtype_of_MsgVoteResp
                  | exact HTnz
                  | intros Hc; exfalso; revert Hc; w32_ne ].
      iIntros "Hphys". wp_auto.
      rewrite send_msgs_app.
      rewrite (_ : (cmsg <$> take (Z.to_nat (sint.Z n)) xs)
                     ++ [msg.mk mtype.VoteResp id id T false]
                 = cmsg <$> take (Z.to_nat (sint.Z (word.add n (W64 1)))) xs);
        last by rewrite Hgrow Hcmsg_self.
      wp_for_post. wp_auto.
      iFrame. iPureIntro. word.
    + (* a peer: read the last entry, log, and send it a [MsgVote] *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raftLog__lastEntryID with "[$Hlog2]") as "%lastID Hlog2".
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok2.
      wp_apply (wp_Logger__logf with "Hlogger2").
      { apply Infof_is_log_method. }
      (* [ctx] is the [campaignTransfer] marker or nil; the model does not
         look at a vote request's context, so both arms run the same tail. *)
      destruct (decide (t = campaignTransfer)) as [->|Hnt].
      * rewrite bool_decide_eq_true_2 //.
        wp_apply wp_string_to_bytes as "%csl [Hcs Hcs_cap]".
        wp_auto.
        iAssert (own_raft_phys cfg r id
                   (send_msgs (become_candidate id s)
                      (cmsg <$> take (Z.to_nat (sint.Z n)) xs)))
          with "[Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2]"
          as "Hphys".
        { rewrite /own_raft_phys. iExists _, _, _, _. iFrame "∗#%". }
        wp_apply (P.wp_raft__send_vote _ _ _ _ _ mtype.Vote with "[$Hphys]");
          try first [ done
                    | by left
                    | apply mtype_of_MsgVote
                    | exact HTnz
                    | intros _; exact Hney ].
        iIntros "Hphys". wp_auto.
        rewrite send_msgs_app.
        rewrite (_ : (cmsg <$> take (Z.to_nat (sint.Z n)) xs)
                       ++ [msg.mk mtype.Vote id y T false]
                   = cmsg <$> take (Z.to_nat (sint.Z (word.add n (W64 1)))) xs);
          last by rewrite Hgrow (Hcmsg_peer y Hney).
        wp_for_post. wp_auto.
        iFrame. iPureIntro. word.
      * rewrite bool_decide_eq_false_2 //. wp_auto.
        iAssert (own_raft_phys cfg r id
                   (send_msgs (become_candidate id s)
                      (cmsg <$> take (Z.to_nat (sint.Z n)) xs)))
          with "[Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2]"
          as "Hphys".
        { rewrite /own_raft_phys. iExists _, _, _, _. iFrame "∗#%". }
        wp_apply (P.wp_raft__send_vote _ _ _ _ _ mtype.Vote with "[$Hphys]");
          try first [ done
                    | by left
                    | apply mtype_of_MsgVote
                    | exact HTnz
                    | intros _; exact Hney ].
        iIntros "Hphys". wp_auto.
        rewrite send_msgs_app.
        rewrite (_ : (cmsg <$> take (Z.to_nat (sint.Z n)) xs)
                       ++ [msg.mk mtype.Vote id y T false]
                   = cmsg <$> take (Z.to_nat (sint.Z (word.add n (W64 1)))) xs);
          last by rewrite Hgrow (Hcmsg_peer y Hney).
        wp_for_post. wp_auto.
        iFrame. iPureIntro. word.
  - (* every voter has been notified *)
    rewrite (_ : Z.to_nat (sint.Z n) = length xs); last word.
    rewrite firstn_all.
    iApply ("HΦ" $! (elements (cfg ∖ {[id]}))).
    iSplitR; [iPureIntro; done|].
    rewrite -HTeq.
    iApply (own_raft_phys_send_perm with "Hphys").
    rewrite Hxs_split /= Hcmsg_self Hpeers //.
*)

End CampaignProof.
