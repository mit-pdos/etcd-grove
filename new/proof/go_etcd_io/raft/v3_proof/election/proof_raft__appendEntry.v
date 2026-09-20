Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__appendEntry.

Module RaftAppendEntryProof (P : RAFT__APPENDENTRY_POSTULATES) : RAFT__APPENDENTRY.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** [own_raft_phys] constrains the outbox only up to permutation, so a state
    may be replaced by any other that agrees on the five scalar fields and
    permutes the outbox.  A copy of [proof_raft__campaign.v]'s lemma of the
    same name, which is [Local] there; needed here to read [send]'s
    [send_msgs s []] back as [s]. *)
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

(** A [send] that the model does not see leaves the state alone. *)
Lemma own_raft_phys_unsend (r : loc) (id : w64) (s0 : nstate.t) :
  own_raft_phys cfg r id (send_msgs s0 []) -∗ own_raft_phys cfg r id s0.
Proof.
  iIntros "H". iApply (own_raft_phys_outbox with "H"); try done.
  rewrite /send_msgs /= app_nil_r //.
Qed.

(** [MsgAppResp] is not one of the four types the model describes, so
    [send_ok]'s third clause applies to it. *)
Lemma mtype_of_MsgAppResp : mtype_of MsgAppResp = None.
Proof.
  rewrite /mtype_of.
  repeat (case_decide as Hc;
          [ exfalso; revert Hc; rewrite /MsgAppResp /MsgVote /MsgVoteResp
              /MsgApp /MsgHeartbeat; intros Hc;
            apply (f_equal uint.Z) in Hc; vm_compute in Hc; discriminate
          | ]).
  done.
Qed.

(** The two facts about the log that [appendEntry] needs but
    [own_raftLog_at] only holds inside: the index layout, and the bound that
    makes one more entry fit.

    The bound is the whole point of [is_Storage]'s [Hbounded] clause: the
    stable prefix is below [2^61] by that contract, the unstable suffix is a
    Go slice and so below [2^63] by [own_slice_len], and their sum is what
    [lastIndex] returns. *)
Lemma own_raftLog_at_facts (l : loc) prev sents uents :
  own_raftLog_at l prev sents uents -∗
  ⌜ log_indices_ok prev (sents ++ uents) ∧
    (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
     + Z.of_nat (length uents) < 2^61 + 2^63)%Z ⌝ ∗
  own_raftLog_at l prev sents uents.
Proof.
  iIntros "H". iNamed "H".
  iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
  { iExact "HisStorage". }
  (* [iNamed] rather than a positional pattern: [is_Storage] is gaining
     clauses (2026-09-20 alone added [Hbounded] and [Snapshot]) and a
     positional pattern silently absorbs the extras into its last binder. *)
  iDestruct "Hsto" as (isv) "#Hs". iNamed "Hs".
  iDestruct ("Hbounded" with "HStorage") as "[%Hstb HStorage]".
  iDestruct (slice_len_Z with "Huents") as %Hul.
  iSplitR.
  { iPureIntro. split; [ done | word ]. }
  iExists lv. iFrame "∗#%".
Qed.

(** ** The batch, as [appendEntry] rewrites it

    The loop sets [es[k].Term = r.Term] and [es[k].Index = li+1+k]; nothing
    else about an entry changes, which is what keeps [Type = EntryNormal]
    true of the appended entries. *)
Definition stamp (tm li : w64) (k : nat) (e : raftpb.Entry.t) : raftpb.Entry.t :=
  e <| raftpb.Entry.Term' := tm |>
    <| raftpb.Entry.Index' := word.add (word.add li (W64 1)) (W64 k) |>.

(** One iteration of the loop, on the list: the prefix already stamped grows
    by one. *)
Lemma stamp_step (tm li : w64) (ents : list raftpb.Entry.t) (n : nat)
    (n' : w64) (e : raftpb.Entry.t) :
  ents !! n = Some e →
  n' = W64 (Z.of_nat n) →
  <[n := e <| raftpb.Entry.Term' := tm |>
            <| raftpb.Entry.Index' := word.add (word.add li (W64 1)) n' |>]>
    (take n (imap (stamp tm li) ents) ++ drop n ents)
  = take (S n) (imap (stamp tm li) ents) ++ drop (S n) ents.
Proof.
  intros He ->.
  change (?e0 <| raftpb.Entry.Term' := tm |>
             <| raftpb.Entry.Index' :=
                  word.add (word.add li (W64 1)) (W64 (Z.of_nat n)) |>)
    with (stamp tm li n e0).
  pose proof (lookup_lt_Some _ _ _ He) as Hlt.
  assert (length (take n (imap (stamp tm li) ents)) = n) as Hlen.
  { rewrite length_take length_imap. lia. }
  erewrite drop_S; last exact He.
  replace n with (length (take n (imap (stamp tm li) ents)) + 0)%nat at 1
    by lia.
  rewrite insert_app_r /=.
  erewrite take_S_r; last first.
  { rewrite list_lookup_imap He //. }
  rewrite -app_assoc //.
Qed.

(** The stamped batch continues the log's index sequence. *)
Lemma stamped_indices (tm li : w64) (prev : raft.entryID.t)
    (pre ents : list raftpb.Entry.t) :
  log_indices_ok prev pre →
  (uint.Z li = uint.Z prev.(raft.entryID.index') + Z.of_nat (length pre))%Z →
  (uint.Z li + Z.of_nat (length ents) + 1 < 2^64)%Z →
  log_indices_ok prev (pre ++ imap (stamp tm li) ents).
Proof.
  intros Hpre Hli Hnw k e Hk.
  apply lookup_app_Some in Hk as [Hk | [Hge Hk]].
  - by apply Hpre.
  - rewrite list_lookup_imap in Hk.
    destruct (ents !! (k - length pre)%nat) as [e'|] eqn:He';
      last by inversion Hk.
    pose proof (lookup_lt_Some _ _ _ He') as Hlt.
    injection Hk as <-. rewrite /stamp /=. word.
Qed.

(** Stamping does not touch [Data] either, so the batch is still all-empty
    when [increaseUncommittedSize] weighs it -- and that call happens
    *after* the loop. *)
Lemma stamped_empty (tm li : w64) (ents : list raftpb.Entry.t) :
  Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) ents →
  Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0)
    (imap (stamp tm li) ents).
Proof.
  intros Hempty. apply Forall_lookup. intros k e Hk.
  rewrite list_lookup_imap in Hk.
  destruct (ents !! k) as [e'|] eqn:He'; last by inversion Hk.
  injection Hk as <-.
  pose proof (Forall_lookup_1 _ _ _ _ Hempty He') as Hd.
  rewrite /stamp /=. exact Hd.
Qed.

(** Stamping does not touch [Type]. *)
Lemma stamped_normal (tm li : w64) (ents : list raftpb.Entry.t) :
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) (imap (stamp tm li) ents).
Proof.
  intros Hnorm. apply Forall_lookup. intros k e Hk.
  rewrite list_lookup_imap in Hk.
  destruct (ents !! k) as [e'|] eqn:He'; last by inversion Hk.
  injection Hk as <-.
  pose proof (Forall_lookup_1 _ _ _ _ Hnorm He') as Hty.
  rewrite /stamp /=. exact Hty.
Qed.

End helpers.

Set Default Proof Using "Type".

  (** [appendEntry] stamps the batch, charges it, appends it, and tells
      itself about it with a self-addressed [MsgAppResp].

      The shape of the proof is set by the two [raftLog] specs being stated
      at a *fixed* log split: the split is opened once, before
      [lastIndex()], and stays open until after [append] -- which is why
      [increaseUncommittedSize] is specified against [r ↦ rv] rather than
      [own_raft_phys] (re-sealing in between would re-quantify the split and
      lose the last index just read). *)
  Lemma wp_raft__appendEntry : wp_raft__appendEntry_body.
  Proof.
    intros_ambient.
    intros cfg r id s es ents.
    intros Hempty Hnorm Hsmall.
    wp_start as "[Hphys Hes]". iNamed "Hphys". wp_auto.
    iDestruct (own_slice_len with "Hes") as %[Hlen Hlen'].
    (* [li := r.raftLog.lastIndex()], at a split that stays open *)
    iDestruct "Hlog" as (prev sents uents) "Hlog".
    iDestruct (own_raftLog_at_facts with "Hlog") as "[[%Hidx %Hbnd] Hlog]".
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
    (* The stamping loop.  [slice.for_range] allocates its **own** counter,
       distinct from the Go-level [i] the body assigns [$key] to, and
       [wp_auto] parks in front of that [GoAlloc] (notes/gotchas.md) -- hence
       the [wp_alloc], and hence two pointers in the invariant: [j] is the
       loop's, [i_ptr] is raft's. *)
    wp_alloc j as "Hj".
    iAssert (∃ (n k : w64),
      "Hj" ∷ j ↦ n ∗
      "i" ∷ i_ptr ↦ k ∗
      "Hes" ∷ es ↦* (take (sint.nat n) (imap (stamp rv.(raft.raft.Term') li) ents)
                     ++ drop (sint.nat n) ents) ∗
      "%Hn" ∷ ⌜ (0 ≤ sint.Z n ≤ Z.of_nat (length ents))%Z ⌝)%I
      with "[Hj i Hes]" as "IH".
    { assert (Z.to_nat (sint.Z (W64 0)) = 0%nat) as Hz0 by word.
      iExists (W64 0), _. iFrame "Hj i".
      rewrite Hz0 take_0 drop_0 app_nil_l. iFrame "Hes". iPureIntro. word. }
    wp_auto.
    wp_for "IH".
    wp_if_destruct.
    - assert (∃ e, ents !! sint.nat n = Some e) as [e He].
      { apply lookup_lt_is_Some_2. word. }
      assert ((take (sint.nat n) (imap (stamp rv.(raft.raft.Term') li) ents)
               ++ drop (sint.nat n) ents) !! sint.nat n = Some e) as Hcur.
      { rewrite lookup_app_r length_take length_imap; last word.
        rewrite lookup_drop.
        replace (sint.nat n `min` length ents)%nat with (sint.nat n) by word.
        rewrite -He. f_equal. word. }
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                  es (sint.Z n) _ (DfracOwn 1) e with "[$Hes]") as "Hes";
        try first [ word | iPureIntro; exact Hcur | tc_solve | done ].
      rewrite decide_True; last word.
      iDestruct (own_slice_elem_acc (sint.Z n) e es (DfracOwn 1) _
                   with "Hes") as "[He Hesback]";
        [ word | exact Hcur | ].
      wp_auto.
      (* the [Index] store has its own bounds [decide]; one [rewrite] does
         not reach it, since ssreflect rewrites only the first occurrence *)
      rewrite decide_True; last word.
      wp_auto.
      iDestruct ("Hesback" with "He") as "Hes".
      rewrite (stamp_step rv.(raft.raft.Term') li ents (sint.nat n) n e He);
        last word.
      wp_for_post.
      iFrame.
      (* the counter moved on by one, so the stamped prefix does too *)
      assert (Z.to_nat (sint.Z (word.add n (W64 1)))
              = S (Z.to_nat (sint.Z n)))%nat as Hsucc by word.
      rewrite Hsucc. iFrame. iPureIntro. word.
    - (* the loop is done: every entry is stamped *)
      assert (sint.nat n = length ents) as Hfull by word.
      rewrite Hfull take_ge; last (rewrite length_imap; lia).
      rewrite drop_ge; last lia.
      rewrite app_nil_r.
      (* the reject path is dead: every payload is empty, and the loop
         rewrote only [Term] and [Index] *)
      assert (Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0)
                (imap (stamp rv.(raft.raft.Term') li) ents)) as Hempty2
        by (by apply stamped_empty).
      wp_apply (wp_raft__increaseUncommittedSize _ _ _ _ _ Hempty2
                  with "[$Hr $Hes]") as "%uc [Hr Hes]".
      wp_apply (wp_traceReplicate with "[$Hes]") as "Hes".
      (* [append]'s three premises *)
      assert (log_indices_ok prev
                (sents ++ uents ++ imap (stamp rv.(raft.raft.Term') li) ents))
        as Hidx2.
      { rewrite app_assoc. apply stamped_indices; [ done | | ].
        - rewrite length_app. lia.
        - lia. }
      assert (Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
                (imap (stamp rv.(raft.raft.Term') li) ents)) as Hnorm2
        by (by apply stamped_normal).
      assert (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
              + Z.of_nat (length uents)
              + Z.of_nat (length (imap (stamp rv.(raft.raft.Term') li) ents))
              + 1 < 2^64)%Z as Hnw2
        by (rewrite length_imap; lia).
      wp_apply (wp_raftLog__append_at _ _ _ _ _ _ _ Hidx2 Hnorm2 Hnw2
                  with "[$Hlog $Hes]")
        as "%li2 (Hlog & Hes & %Hli2)".
      (* re-seal: the log at the longer split, then the struct *)
      iAssert (own_raftLog rv.(raft.raft.raftLog')) with "[Hlog]" as "Hlog".
      { iExists prev, sents,
          (uents ++ imap (stamp rv.(raft.raft.Term') li) ents). iFrame. }
      (* [rv.(id')] rather than [id]: [word] runs [subst] over the context,
         and [own_raft_phys]'s [Hid : rv.(id') = id] is exactly the shape it
         eliminates, so by here the binder [id] is gone and every occurrence
         -- [HΦ] included -- reads [rv.(raft.raft.id')]. *)
      iAssert (own_raft_phys cfg r rv.(raft.raft.id') s)
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
        as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
          done. }
      (* the self-addressed [MsgAppResp]: [send_ok]'s third clause *)
      wp_apply (P.wp_raft__send with "[$Hphys]");
        [ done
        | right; right; split_and!;
          [ apply mtype_of_MsgAppResp | w32_ne | w32_ne | done
          | by intros _ | done ]
        | ].
      iIntros "Hphys". wp_auto.
      iDestruct (own_raft_phys_unsend with "Hphys") as "Hphys".
      iApply ("HΦ" $! (imap (stamp rv.(raft.raft.Term') li) ents)).
      iFrame.
  Qed.

End RaftAppendEntryProof.
