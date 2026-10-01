Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__appendEntry.

Module RaftAppendEntryProof (P : RAFT__APPENDENTRY_POSTULATES) : RAFT__APPENDENTRY.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).


(** The two facts about the log that [appendEntry] needs but
    [own_raftLog] only holds inside: the index layout, and the bound that
    makes one more entry fit.

    The bound is the whole point of [is_Storage]'s [Hbounded] clause: the
    stable prefix is below [2^61] by that contract, the unstable suffix is a
    Go slice and so below [2^63] by [own_slice_len], and their sum is what
    [lastIndex] returns. *)
Lemma own_raftLog_facts (l : loc) prev sents uents cm ap :
  own_raftLog l (logstate.mk prev sents uents cm ap) -∗
  ⌜ log_indices_ok prev (sents ++ uents) ∧
    (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
     + Z.of_nat (length uents) < 2^61 + 2^63)%Z ⌝ ∗
  own_raftLog l (logstate.mk prev sents uents cm ap).
Proof.
  iIntros "H". iNamed "H".
  iEval (rewrite /own_raftLog_core /=) in "Hcore".
  iDestruct "Hcore" as (stored) "Hcore". iNamed "Hcore".
  pose proof (prefix_length _ _ Hstored) as Hstlen.
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
  reseal_raftLog.
Qed.

(** ** The batch, as [appendEntry] rewrites it: [stamp] ([defs.v]). *)

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

      The log's state is in [nstate.t] ([nstate.logst]), so the
      [lastIndex()] read and the [append] are both stated at [s]'s log
      state, and the calls in between ([r.Term] loads,
      [increaseUncommittedSize]) leave it alone: nothing is lent.  (Until
      2026-09-28 the tracker and the log were lent out of [own_raft_phys]
      for that stretch, to keep the log split fixed.) *)
  Lemma wp_raft__appendEntry : wp_raft__appendEntry_body.
  Proof.
    intros_ambient.
    intros cfg r id s es ents.
    intros Hempty Hnorm Hsmall.
    wp_start as "[Hphys Hes]". wp_auto. wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_slice_len with "Hes") as %[Hlen Hlen'].
    (* [li := r.raftLog.lastIndex()], at a split that stays open *)
    (* the log is read at the state [s] records, and put back unchanged *)
    destruct (s.(nstate.logst)) as [prev sents uents lcm lap] eqn:Hls.
    iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
    iEval (rewrite Hls) in "Hlog".
    iDestruct (own_raftLog_facts with "Hlog") as "[[%Hidx %Hbnd] Hlog]".
    wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap) with "[$Hlog]")
      as "%li [Hlog %Hli]".
    cbn [logstate.prev logstate.sents logstate.uents] in Hli.
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys".
    { destruct s; simpl in Hls; subst. done. }
    (* The stamping loop.  [slice.for_range] allocates its **own** counter,
       distinct from the Go-level [i] the body assigns [$key] to, and
       [wp_auto] parks in front of that [GoAlloc] (notes/gotchas.md) -- hence
       the [wp_alloc], and hence two pointers in the invariant: [j] is the
       loop's, [i_ptr] is raft's. *)
    wp_alloc j as "Hj".
    iAssert (∃ (n k : w64),
      "Hj" ∷ j ↦ n ∗
      "i" ∷ i_ptr ↦ k ∗
      "Hes" ∷ es ↦* (take (sint.nat n) (imap (stamp s.(nstate.term) li) ents)
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
      assert ((take (sint.nat n) (imap (stamp s.(nstate.term) li) ents)
               ++ drop (sint.nat n) ents) !! sint.nat n = Some e) as Hcur.
      { rewrite lookup_app_r length_take length_imap; last word.
        rewrite lookup_drop.
        replace (sint.nat n `min` length ents)%nat with (sint.nat n) by word.
        rewrite -He. f_equal. word. }
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                  es (sint.Z n) _ (DfracOwn 1) e with "[$Hes]") as "Hes";
        try first [ word | iPureIntro; exact Hcur | tc_solve | done ].
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
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
      rewrite (stamp_step s.(nstate.term) li ents (sint.nat n) n e He);
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
                (imap (stamp s.(nstate.term) li) ents)) as Hempty2
        by (by apply stamped_empty).
      wp_apply (wp_raft__increaseUncommittedSize _ _ _ _ _ _ _ Hempty2
                  with "[$Hphys $Hes]") as "[Hphys Hes]".
      wp_apply wp_traceReplicate. try wp_auto.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      (* [append]'s three premises *)
      assert (log_indices_ok prev
                (sents ++ uents ++ imap (stamp s.(nstate.term) li) ents))
        as Hidx2.
      { rewrite app_assoc. apply stamped_indices; [ done | | ].
        - rewrite length_app. lia.
        - lia. }
      assert (Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
                (imap (stamp s.(nstate.term) li) ents)) as Hnorm2
        by (by apply stamped_normal).
      assert (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
              + Z.of_nat (length uents)
              + Z.of_nat (length (imap (stamp s.(nstate.term) li) ents))
              + 1 < 2^64)%Z as Hnw2
        by (rewrite length_imap; lia).
      iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
      iEval (rewrite Hls) in "Hlog".
      (* [append]'s widened spec: the stamped batch continues the log, so
         it is a plain [log_append] and nothing is adopted *)
      iDestruct (own_raftLog_committed with "Hlog") as "[%Hcmb Hlog]".
      cbn [logstate.prev logstate.sents logstate.uents logstate.committed
           logstate.applied] in Hcmb.
      assert (∀ (k2 : nat) e, imap (stamp s.(nstate.term) li) ents !! k2 = Some e →
                uint.Z e.(raftpb.Entry.Index')
                = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents) + 1 + k2)%Z as Hk2.
      { intros k2 e Hk. specialize (Hidx2 (length sents + length uents + k2)%nat e).
        rewrite app_assoc lookup_app_r in Hidx2; last (rewrite length_app; lia).
        rewrite length_app in Hidx2.
        replace (length sents + length uents + k2 - (length sents + length uents))%nat
          with k2 in Hidx2 by lia.
        specialize (Hidx2 Hk). lia. }
      destruct (log_truncate_append_cont (logstate.mk prev sents uents lcm lap)
                  (imap (stamp s.(nstate.term) li) ents)) as [Htac Hado].
      { intros e0 He0. specialize (Hk2 0%nat e0 He0). simpl. lia. }
      iAssert (if log_adopts (logstate.mk prev sents uents lcm lap)
                    (imap (stamp s.(nstate.term) li) ents)
               then ⌜ DfracOwn 1 = DfracDiscarded ⌝ ∗ own_slice_cap raftpb.Entry.t es (DfracOwn 1)
               else True)%I as "Hadopt".
      { rewrite Hado. done. }
      wp_apply (wp_raftLog__append _ (logstate.mk prev sents uents lcm lap)
                  (imap (stamp s.(nstate.term) li) ents) _ _
                  ltac:(intros e0 He0; pose proof (Hk2 0%nat e0 He0); simpl;
                        split_and!; [lia | lia | | ];
                        [ intros k2 e Hk; specialize (Hk2 k2 e Hk); lia
                        | rewrite length_imap in Hnw2 |- *; lia ])
                  Hnorm2
                  with "[$Hlog $Hes $Hadopt]")
        as "%li2 (Hlog & Hes & %Hsplit2 & %Hli2)".
      rewrite Htac Hado.
      rewrite Htac /log_append /= in Hli2.
      rewrite length_app in Hli2.
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      (* [li] is [log_last] of the log it was read from: [lastIndex()]
         cannot wrap ([Hbnd]) *)
      assert (log_last (logstate.mk prev sents uents lcm lap) = li) as Hlast.
      { rewrite /log_last /=. apply word.unsigned_inj.
        pose proof (word.unsigned_range prev.(raft.entryID.index')).
        rewrite word.unsigned_of_Z_nowrap; lia. }
      set s' := s <| nstate.logst := log_append (logstate.mk prev sents uents lcm lap)
                     (imap (stamp s.(nstate.term)
                              (log_last (logstate.mk prev sents uents lcm lap))) ents) |>.
      iDestruct (own_raft_phys_eq _ _ _ _ s' with "Hphys") as "Hphys".
      { rewrite /s' Hlast. done. }
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      (* the self-acknowledgement: [send_ok]'s [MsgAppResp] clause, with no
         entries *)
      wp_apply (P.wp_raft__send _ _ _ _ _ []
                  [self_ack id s'] with "[$Hphys]").
      { done. }
      { right; right; right; left. split_and!; [done|done|].
        rewrite /self_ack /abs_msg_from /=. repeat f_equal.
        rewrite /s' /log_append /=. symmetry. rewrite /log_last /=.
        apply word.unsigned_inj. rewrite Hli2 /= !length_app !length_imap.
        rewrite length_imap in Hnw2. rewrite word.unsigned_of_Z_nowrap; [lia|].
        pose proof (word.unsigned_range prev.(raft.entryID.index')). lia. }
      { iApply own_slice_nil. }
      iIntros "Hphys". wp_auto.
      iApply "HΦ". rewrite Hlast. iFrame.
  Qed.

End RaftAppendEntryProof.
