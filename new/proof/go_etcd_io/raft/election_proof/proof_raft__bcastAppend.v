Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastAppend.

Module RaftBcastAppendProof (P : RAFT__BCASTAPPEND_POSTULATES) : RAFT__BCASTAPPEND.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Local Lemma send_msgs_app (s0 : nstate.t) (ms1 ms2 : list msg.t) :
  send_msgs (send_msgs s0 ms1) ms2 = send_msgs s0 (ms1 ++ ms2).
Proof. rewrite /send_msgs /= app_assoc //. Qed.


(** ** [bcastAppend]

    The body ([raft__bcastAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3267) is

      r.trk.Visit(func(id uint64, _ *Progress) {
        if id == r.id { return }
        r.sendAppend(id)
      })

    so the whole proof is the choice of [Visit]'s caller invariant [I] and
    the closure obligation.

    **[I] is a wand, and that is the point.**  [Visit] takes the tracker
    object -- the [trk] field and [own_tracker] -- and lends it to the
    closure; but [r.sendAppend(id)] is specified on [own_raft_phys], which
    includes that object.  So [I] carries exactly "the raft struct with a
    tracker-shaped hole", the wand of [own_raft_phys_tracker_prvals]:

      ∃ ms, r_ptr ↦ r ∗ ⌜ repl_sends id s ms ⌝ ∗ ⌜ prvals_match pvsx = prvals_match s.prvals ⌝ ∗
            (∀ tvx pvsx, r.[trk] ↦ tvx -∗
                    own_tracker cfg tvx (trk.mk s.votes s.progress pvsx) -∗
                    own_raft_phys cfg r id (send_msgs s ms <| prvals := pvsx |>))

    quantified over the [Progress] values because [sendAppend] changes them
    ([nstate.prvals]), and over the field value because [own_raft_phys]
    hides it: after
    [sendAppend] the tracker is split off again at whatever value the
    struct now holds.  That is also why [visit_closure]'s postcondition is
    existential in the tracker value; see [inv_tracker.v].  What it does
    pin is the progress map, [nstate.progress], which is the index of the
    wand's [own_tracker].  The closure fills the hole with what it was
    handed, reads [r.id], calls [sendAppend] on the whole struct, and
    splits the tracker off again for [Visit].

    [ms] accumulates.  Each iteration either sends nothing (the peer is the
    leader itself, or [maybeSendAppend] declined) or adds messages
    [repl_sends] allows, which is closed under concatenation; no [Match]
    moves.  That is the whole content of the postcondition.  One [App] per peer would be
    false; see [spec_raft__bcastAppend.v]. *)
Lemma wp_bcast (r : loc) (id : w64) (s : nstate.t) :
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastAppend" #()
  {{{ (ms : list msg.t) pvs, RET #();
      own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
      ⌜ repl_sends id s ms ⌝ ∗
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.
Proof.
  wp_start as "Hphys". wp_auto.
  iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
  iDestruct (own_raft_phys_tracker_prvals with "Hphys")
    as (tv) "(Htrkf & Htrk & Hrest)".
  wp_apply (wp_ProgressTracker__Visit _ _ _ (trk.mk s.(nstate.votes) s.(nstate.progress) _) _
              (λ _ pvsx, ∃ (ms : list msg.t),
                 "rp" ∷ r_ptr ↦ r ∗
                 "%Hms" ∷ ⌜ repl_sends id s ms ⌝ ∗
                 "%Hmm" ∷ ⌜ prvals_match pvsx = prvals_match s.(nstate.prvals) ⌝ ∗
                 "Hrest" ∷ (∀ tvx pvsx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                          own_tracker cfg tvx (trk.mk s.(nstate.votes) s.(nstate.progress) pvsx) -∗
                          own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvsx |>)))%I
              with "[$Htrkf $Htrk r Hrest]").
  { iSplitL "r Hrest".
    { iExists []. iFrame "r". iSplitR; first (iPureIntro; by apply Forall_nil).
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
      iExists ms. iFrame "rp". iSplitR; first done.
      iSplitR; first (iPureIntro; simpl; rewrite (insert_id _ _ _ Hpvi) //).
      iIntros (tvx pvsx) "Hf Ht". iDestruct ("Hrest" with "Hf Ht") as "Hphys".
      iApply (own_raft_phys_eq with "Hphys"). reflexivity.
    - (* a peer: [sendAppend] may add [App]s and change [Progress]es *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft__sendAppend _ _ _ _ i Hii Hicfg with "[$Hphys]")
        as "%ms' %pvs' (Hphys & %Hms' & %Hmm')".
      try wp_auto.
      iDestruct (own_raft_phys_tracker_prvals with "Hphys")
        as (tv1) "(Htrkf & Htrk & Hrest)".
      iApply "HΦ". iExists tv1, _. iFrame "Htrkf Htrk".
      iExists (ms ++ ms'). iFrame "rp".
      iSplitR.
      { iPureIntro. apply repl_sends_app; [ exact Hms | ].
        exact (proj1 (repl_sends_send_prvals id s ms _ ms') Hms'). }
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

  Lemma wp_raft__bcastAppend : wp_raft__bcastAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    by apply wp_bcast.
  Qed.

End RaftBcastAppendProof.
