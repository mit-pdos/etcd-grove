Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__bcastAppend.

Module RaftBcastAppendProof (P : RAFT__BCASTAPPEND_POSTULATES) : RAFT__BCASTAPPEND.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** Split the [trk] field out of the whole-struct points-to, keeping a
    continuation wand that accepts *any* new field value.  Same lemma as
    [proof_raft__reset.v]'s; both are [Local] to their functor, so it is
    copied rather than shared (see that file for why the generated
    [AccessStrict] instance will not do). *)
Local Lemma raft_split_trk (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (∀ tv, l.[raft.raft.t, "trk"] ↦ tv -∗ l ↦ (rv <| raft.raft.trk' := tv |>)).
Proof.
  iIntros "Hr".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr".
  iDestruct "Hr" as "[Hf %Hnn]". iNamed "Hf".
  iFrame "trk".
  iIntros (tv) "Htv".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame "∗%".
Qed.

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

    **[I] is a wand, and that is the point.**  The closure is handed the
    [trk] *field* ([trk ↦ tv]) and, through [visit_closure]'s accessor, the
    whole [own_tracker]; but [r.sendAppend(id)] is specified on
    [own_raft_phys], which packages the entire struct -- the [trk] field
    included -- as [∃ rv, r ↦ rv ∗ …].  So [I] carries exactly "the raft
    struct with a tracker-shaped hole":

      ∃ ms, r_ptr ↦ r ∗ ⌜ app_sends id s.term ms ⌝ ∗
            (∀ tvx, r.[trk] ↦ tvx -∗ tvx.Progress ↦$□ s.progress -∗
                    own_tracker cfg tvx s.votes -∗
                    own_raft_phys cfg r id (send_msgs s ms))

    quantified over the field value because [own_raft_phys] hides the
    struct value: after [sendAppend] the struct comes back as a fresh
    [rv'], and nothing in the predicate says [rv'.(trk') = tv].  That is
    also why [visit_closure]'s postcondition is existential in the tracker
    value; see [inv_tracker.v].  What it does pin is the progress map,
    [nstate.progress], which is what the wand's second premise is.

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
  iNamed "Hphys".
  iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk".
  iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback]".
  (* the hole, at [ms = []] *)
  iAssert (∃ (ms : list msg.t),
             "rp" ∷ r_ptr ↦ r ∗
             "%Hms" ∷ ⌜ app_sends id s.(nstate.term) ms ⌝ ∗
             "Hrest" ∷ (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                          tvx.(tracker.ProgressTracker.Progress') ↦$□ s.(nstate.progress) -∗
                          own_tracker cfg tvx s.(nstate.votes) -∗
                          own_raft_phys cfg r id (send_msgs s ms)))%I
    with "[r Hrback Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "HI".
  { iExists []. iFrame "r". iSplitL ""; first (iPureIntro; by apply Forall_nil).
    iIntros (tvx) "Hf #Hpx Htk".
    iDestruct ("Hrback" $! tvx with "Hf") as "Hr".
    iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htk") as "Htk".
    iApply own_raft_phys_send_nil.
    iApply (own_raft_phys_intro _ _ _ s with
             "Hr Hlogger Hpx Htk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
      done. }
  wp_apply (wp_ProgressTracker__Visit _ _ _ _ s.(nstate.progress) _
              (∃ (ms : list msg.t),
                 "rp" ∷ r_ptr ↦ r ∗
                 "%Hms" ∷ ⌜ app_sends id s.(nstate.term) ms ⌝ ∗
                 "Hrest" ∷ (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                          tvx.(tracker.ProgressTracker.Progress') ↦$□ s.(nstate.progress) -∗
                          own_tracker cfg tvx s.(nstate.votes) -∗
                          own_raft_phys cfg r id (send_msgs s ms)))%I
              with "[$Htrkf $Htrk $HI $Hprs]").
  { (* the closure *)
    iModIntro. iIntros (i pr tv0).
    wp_start as "(%Hicfg & %Hpri & %HmaxI & Htrkf & #Hprsv & Hpr & Hback & HI)".
    iNamed "HI".
    iDestruct ("Hback" with "Hpr") as "Htrk".
    iDestruct ("Hrest" $! tv0 with "Htrkf Hprsv Htrk") as "Hphys".
    (* [iNamed] stops at the first name already in use, and the enclosing
       proof's [Hlogger] is still in the intuitionistic context -- it would
       leave [Hlok]/[Hlogger]/[Hmisc] bundled up inside "Hphys".  Clear it
       first; the struct we are opening carries its own. *)
    iClear "Hlogger Hprs Hprsv".
    iNamed "Hphys".
    iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk".
    wp_auto.
    destruct (decide (i = rv0.(raft.raft.id'))) as [Hii|Hii].
    - (* the leader itself: nothing is sent *)
      assert (bool_decide (i = rv0.(raft.raft.id')) = true) as Hbi
        by (apply bool_decide_eq_true_2; done).
      rewrite Hbi /=. wp_auto.
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback0]".
      iApply "HΦ". iExists rv0.(raft.raft.trk').
      iFrame "Htrkf Htrk Hprs".
      iExists ms. iFrame "rp". iSplitL ""; first (iPureIntro; exact Hms).
      iIntros (tvx) "Hf #Hpx Htk".
      iDestruct ("Hrback0" $! tvx with "Hf") as "Hr".
      iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htk") as "Htk".
      (* the abstract state has to be given: [Htk] alone would unify it
         with [s], not with [send_msgs s ms] *)
      iApply (own_raft_phys_intro cfg r id (send_msgs s ms) with
               "Hr Hlogger Hpx Htk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        done.
    - (* a peer: [sendAppend] may add [App]s *)
      assert (bool_decide (i = rv0.(raft.raft.id')) = false) as Hbi
        by (apply bool_decide_eq_false_2; done).
      rewrite Hbi /=. wp_auto.
      iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
      iAssert (own_raft_phys cfg r id (send_msgs s ms))
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
        as "Hphys".
      { iApply (own_raft_phys_intro cfg r id (send_msgs s ms) with
                 "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
          done. }
      assert (i ≠ id) as Hne by congruence.
      (* [Hlent] is about [s]; the state [sendAppend] runs at is
         [send_msgs s ms], so it is passed explicitly *)
      wp_apply (wp_raft__sendAppend _ _ _ (send_msgs s ms) i Hne Hicfg Hlent
                  with "[$Hphys]")
        as "%ms' [Hphys %Hms']".
      try wp_auto.
      rewrite send_msgs_app.
      (* [clear dependent]: the pure conjuncts of the first [iNamed]
         ([Hid0], [Hterm0], …) mention [rv0]. *)
      iClear "Hlogger Hprs".
      clear dependent rv0. clear dependent msgs0.
      clear dependent msgsAA0. clear dependent lok0.
      iNamed "Hphys".
      iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk".
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback0]".
      iApply "HΦ". iExists rv0.(raft.raft.trk').
      iFrame "Htrkf Htrk Hprs".
      iExists (ms ++ ms'). iFrame "rp". iSplitL "".
      { iPureIntro. apply app_sends_app; [ exact Hms | exact Hms' ]. }
      iIntros (tvx) "Hf #Hpx Htk".
      iDestruct ("Hrback0" $! tvx with "Hf") as "Hr".
      iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htk") as "Htk".
      iApply (own_raft_phys_intro cfg r id (send_msgs s (ms ++ ms')) with
               "Hr Hlogger Hpx Htk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        done. }
  iIntros "H". iDestruct "H" as (tvfin) "(Htrkf & Htrk & #Hprsfin & HI)".
  iNamed "HI".
  iDestruct ("Hrest" $! tvfin with "Htrkf Hprsfin Htrk") as "Hphys".
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
