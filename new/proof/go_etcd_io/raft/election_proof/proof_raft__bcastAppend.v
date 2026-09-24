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

Local Lemma app_sends_app (id t : w64) (ms1 ms2 : list msg.t) :
  app_sends id t ms1 → app_sends id t ms2 → app_sends id t (ms1 ++ ms2).
Proof. rewrite /app_sends. apply Forall_app_2. Qed.

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
    tracker-shaped hole", the wand of [own_raft_phys_tracker_same]:

      ∃ ms, r_ptr ↦ r ∗ ⌜ app_sends id s.term ms ⌝ ∗
            (∀ tvx, r.[trk] ↦ tvx -∗ own_tracker cfg tvx s.votes s.progress -∗
                    own_raft_phys cfg r id (send_msgs s ms))

    quantified over the field value because [own_raft_phys] hides it: after
    [sendAppend] the tracker is split off again at whatever value the
    struct now holds.  That is also why [visit_closure]'s postcondition is
    existential in the tracker value; see [inv_tracker.v].  What it does
    pin is the progress map, [nstate.progress], which is the index of the
    wand's [own_tracker].  The closure fills the hole with what it was
    handed, reads [r.id], calls [sendAppend] on the whole struct, and
    splits the tracker off again for [Visit].

    [ms] accumulates.  Each iteration either sends nothing (the peer is the
    leader itself, or [maybeSendAppend] declined) or adds [App]s from [id]
    at [s.term], and [app_sends] is closed under concatenation -- which is
    the whole content of the postcondition.  One [App] per peer would be
    false; see [spec_raft__bcastAppend.v]. *)
Lemma wp_bcast (r : loc) (id : w64) (s : nstate.t) :
  s.(nstate.lent) = None →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastAppend" #()
  {{{ (ms : list msg.t), RET #();
      own_raft_phys cfg r id (send_msgs s ms) ∗
      ⌜ app_sends id s.(nstate.term) ms ⌝ }}}.
Proof.
  intros Hlent.
  wp_start as "Hphys". wp_auto.
  iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
  (* [Hlent] is about [s]; it is passed at [send_msgs s ms] throughout,
     which differs from [s] only in the outbox *)
  iDestruct (own_raft_phys_tracker_same _ _ _ (send_msgs s []) Hlent with "Hphys")
    as (tv) "(Htrkf & Htrk & Hrest)".
  wp_apply (wp_ProgressTracker__Visit _ _ _ s.(nstate.votes) s.(nstate.progress) _
              (∃ (ms : list msg.t),
                 "rp" ∷ r_ptr ↦ r ∗
                 "%Hms" ∷ ⌜ app_sends id s.(nstate.term) ms ⌝ ∗
                 "Hrest" ∷ (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                          own_tracker cfg tvx s.(nstate.votes) s.(nstate.progress) -∗
                          own_raft_phys cfg r id (send_msgs s ms)))%I
              with "[$Htrkf $Htrk r Hrest]").
  { iSplitL "r Hrest".
    { iExists []. iFrame "r Hrest". iPureIntro. by apply Forall_nil. }
    (* the closure *)
    iModIntro. iIntros (i pr tv0).
    wp_start as "(%Hicfg & %Hpri & %HmaxI & Htrkf & Hpr & Hback & HI)".
    iNamed "HI".
    iDestruct ("Hback" with "Hpr") as "Htrk".
    iDestruct ("Hrest" $! tv0 with "Htrkf Htrk") as "Hphys".
    wp_auto. wp_raft_field.
    destruct (decide (i = id)) as [Hii|Hii].
    - (* the leader itself: nothing is sent *)
      rewrite bool_decide_eq_true_2 //. wp_auto.
      iDestruct (own_raft_phys_tracker_same _ _ _ (send_msgs s ms) Hlent with "Hphys")
        as (tv1) "(Htrkf & Htrk & Hrest)".
      iApply "HΦ". iExists tv1. iFrame "Htrkf Htrk".
      iExists ms. iFrame "rp Hrest". done.
    - (* a peer: [sendAppend] may add [App]s *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft__sendAppend _ _ _ (send_msgs s ms) i Hii Hicfg Hlent
                  with "[$Hphys]")
        as "%ms' [Hphys %Hms']".
      try wp_auto.
      rewrite send_msgs_app.
      iDestruct (own_raft_phys_tracker_same _ _ _ (send_msgs s (ms ++ ms')) Hlent
                   with "Hphys")
        as (tv1) "(Htrkf & Htrk & Hrest)".
      iApply "HΦ". iExists tv1. iFrame "Htrkf Htrk".
      iExists (ms ++ ms'). iFrame "rp Hrest".
      iPureIntro. apply app_sends_app; [ exact Hms | exact Hms' ]. }
  iIntros "H". iDestruct "H" as (tvfin) "(Htrkf & Htrk & HI)".
  iNamed "HI".
  iDestruct ("Hrest" $! tvfin with "Htrkf Htrk") as "Hphys".
  wp_auto.
  iApply ("HΦ" $! ms). by iFrame.
Qed.

End helpers.

Set Default Proof Using "Type".

  Lemma wp_raft__bcastAppend : wp_raft__bcastAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s Hlent.
    by apply wp_bcast.
  Qed.

End RaftBcastAppendProof.
