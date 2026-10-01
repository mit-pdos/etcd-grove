(** * Pure functions on a raft log, shared by the protocol model and the
    [raftLog] specs.

    A log is a compaction boundary [b : raft.entryID.t] -- the last entry
    whose payload has been discarded but whose term is still known -- and the
    entries after it, [es : list raftpb.Entry.t], at indices
    [b.index + 1, b.index + 2, ...] ([plog_wf]).  This is exactly how
    [own_raftLog] ([inv_raftlog.v]) describes the physical log
    ([prev], [sents ++ uents]), and it is what the protocol state
    ([pstate.t], [protocol.v]) carries, so one set of functions serves both:
    a [raftLog] method's spec says it computes [plog_f prev (sents ++ uents)
    args], and the model's rule says the node moves to [plog_f base log
    args].  Each function mirrors one Go function of [log.go] /
    [log_unstable.go], named in its comment; read the Go before changing
    one.

    Entries are the wire type [raftpb.Entry.t]: [Term'], [Index'], [Type'],
    [Data'].  Only the first two are ever read here.  See
    notes/raft-replication-model.md. *)

Require Export New.proof.proof_prelude.
Require Export New.code.go_etcd_io.raft.v3.

Definition ent_id (e : raftpb.Entry.t) : raft.entryID.t :=
  raft.entryID.mk e.(raftpb.Entry.Term') e.(raftpb.Entry.Index').

(** Contiguous indices from [b.index + 1].  The same statement as
    [log_indices_ok] ([inv_raftlog.v]). *)
Definition plog_wf (b : raft.entryID.t) (es : list raftpb.Entry.t) : Prop :=
  ∀ (k : nat) e, es !! k = Some e →
    (uint.Z e.(raftpb.Entry.Index') = uint.Z b.(raft.entryID.index') + S k)%Z.

(** [lastIndex()], as a [Z]: [b.index + |es|]. *)
Definition plog_last_index_Z (b : raft.entryID.t) (es : list raftpb.Entry.t) : Z :=
  uint.Z b.(raft.entryID.index') + Z.of_nat (length es).

(** [lastEntryID()]: the last entry's id, or [b] for an empty suffix. *)
Definition plog_last (b : raft.entryID.t) (es : list raftpb.Entry.t) : raft.entryID.t :=
  match list.last es with Some e => ent_id e | None => b end.

(** [term(i)]: [Some t] on [b.index ≤ i ≤ b.index + |es|], [None] outside.
    Same shape as [term_at] ([inv_storage.v]) but total: [term_at] is only
    meaningful under its range premise, this is meaningful everywhere, which
    is what [matchTerm]'s [bool] result needs. *)
Definition plog_term_at (b : raft.entryID.t) (es : list raftpb.Entry.t) (i : w64)
  : option w64 :=
  if decide (uint.Z i < uint.Z b.(raft.entryID.index'))%Z then None
  else if decide (uint.Z i = uint.Z b.(raft.entryID.index'))%Z
  then Some b.(raft.entryID.term')
  else (λ e, e.(raftpb.Entry.Term')) <$>
         (es !! Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index') - 1)).

(** [matchTerm(id)]: the log has [id.term] at [id.index]. *)
Definition plog_matches (b : raft.entryID.t) (es : list raftpb.Entry.t)
    (id : raft.entryID.t) : Prop :=
  plog_term_at b es id.(raft.entryID.index') = Some id.(raft.entryID.term').

#[global] Instance plog_matches_dec b es id : Decision (plog_matches b es id).
Proof. rewrite /plog_matches. apply _. Defined.

(** [findConflict(ents)]: the index of the first entry of [ents] the log
    does not have (a different term there, or nothing there); [0] if the
    log has them all. *)
Fixpoint plog_find_conflict (b : raft.entryID.t) (es : list raftpb.Entry.t)
    (ents : list raftpb.Entry.t) : w64 :=
  match ents with
  | [] => W64 0
  | e :: ents' =>
      if decide (plog_matches b es (ent_id e))
      then plog_find_conflict b es ents'
      else e.(raftpb.Entry.Index')
  end.

(** The entries of the log from index [i] on (empty when [i] is past the
    end; the whole suffix when [i ≤ b.index + 1]). *)
Definition plog_from (b : raft.entryID.t) (es : list raftpb.Entry.t) (i : w64)
  : list raftpb.Entry.t :=
  drop (Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index') - 1)) es.

(** [unstable.truncateAndAppend(ents)] seen at the whole log: keep the
    entries below [ents[0].Index], then [ents].  Covers all three arms of
    the Go function (append in place, replace the unstable suffix, truncate
    then append); for an empty batch nothing changes. *)
Definition plog_truncate_append (b : raft.entryID.t) (es : list raftpb.Entry.t)
    (ents : list raftpb.Entry.t) : list raftpb.Entry.t :=
  match ents with
  | [] => es
  | e0 :: _ =>
      take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z b.(raft.entryID.index') - 1)) es
      ++ ents
  end.

(** [raftLog.maybeAppend(a, committed)] without the commit: [None] when
    [a.prev] does not match; otherwise the new last index
    [a.prev.index + |a.entries|] and the new entry list -- unchanged if there
    is no conflict, else [truncateAndAppend] of the batch from the conflict
    on ([a.entries[ci-offset:]] with [offset = a.prev.index + 1]). *)
Definition plog_maybe_append (b : raft.entryID.t) (es : list raftpb.Entry.t)
    (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
  : option (w64 * list raftpb.Entry.t) :=
  if decide (plog_matches b es prev) then
    let ci := plog_find_conflict b es ents in
    let es' :=
      if decide (ci = W64 0) then es
      else plog_truncate_append b es
             (drop (Z.to_nat (uint.Z ci - uint.Z prev.(raft.entryID.index') - 1)) ents) in
    Some (W64 (uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents)), es')
  else None.

(** [commitTo(tocommit)]: never decreases. *)
Definition plog_commit_to (committed tocommit : w64) : w64 :=
  if decide (uint.Z committed < uint.Z tocommit)%Z then tocommit else committed.

(** [isUpToDate(their)]: [their] is at least as recent as our last entry. *)
Definition plog_up_to_date (b : raft.entryID.t) (es : list raftpb.Entry.t)
    (their : raft.entryID.t) : bool :=
  let l := plog_last b es in
  bool_decide ((uint.Z l.(raft.entryID.term') < uint.Z their.(raft.entryID.term'))%Z ∨
               (their.(raft.entryID.term') = l.(raft.entryID.term') ∧
                (uint.Z l.(raft.entryID.index') ≤ uint.Z their.(raft.entryID.index'))%Z)).

(** ** Basic facts *)

Lemma plog_wf_app b es1 es2 :
  plog_wf b (es1 ++ es2) ↔
  plog_wf b es1 ∧
  (∀ (k : nat) e, es2 !! k = Some e →
     (uint.Z e.(raftpb.Entry.Index') = uint.Z b.(raft.entryID.index')
                                        + Z.of_nat (length es1) + S k)%Z).
Proof.
  rewrite /plog_wf. split.
  - intros H. split.
    + intros k e Hk. apply (H k e). rewrite lookup_app_l //. by eapply lookup_lt_Some.
    + intros k e Hk. specialize (H (length es1 + k)%nat e).
      rewrite lookup_app_r in H; [|lia].
      replace (length es1 + k - length es1)%nat with k in H by lia.
      specialize (H Hk). lia.
  - intros [H1 H2] k e Hk.
    destruct (decide (k < length es1)%nat) as [Hlt|Hge].
    + rewrite lookup_app_l // in Hk. by apply H1.
    + rewrite lookup_app_r in Hk; [|lia]. specialize (H2 _ _ Hk). lia.
Qed.

Lemma plog_wf_take b es n : plog_wf b es → plog_wf b (take n es).
Proof.
  intros H k e Hk. apply lookup_take_Some in Hk as [Hk _]. by apply H.
Qed.

(** In range, [plog_term_at] is the term of the entry stored there. *)
Lemma plog_term_at_lookup b es (i : w64) (k : nat) e :
  es !! k = Some e →
  (uint.Z i = uint.Z b.(raft.entryID.index') + S k)%Z →
  plog_term_at b es i = Some e.(raftpb.Entry.Term').
Proof.
  intros Hk Hi. rewrite /plog_term_at.
  rewrite decide_False; [|lia]. rewrite decide_False; [|lia].
  replace (Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index') - 1)) with k by lia.
  rewrite Hk //.
Qed.

Lemma plog_term_at_base b es :
  plog_term_at b es b.(raft.entryID.index') = Some b.(raft.entryID.term').
Proof. rewrite /plog_term_at decide_False; [|lia]. rewrite decide_True //. Qed.

Lemma plog_term_at_Some_range b es i t :
  plog_term_at b es i = Some t →
  (uint.Z b.(raft.entryID.index') ≤ uint.Z i ≤ plog_last_index_Z b es)%Z.
Proof.
  rewrite /plog_term_at /plog_last_index_Z.
  case_decide; [done|]. case_decide; [intros; lia|].
  destruct (es !! _) eqn:Hk; [|done]. intros _.
  apply lookup_lt_Some in Hk. lia.
Qed.

Lemma plog_term_at_None_range b es i :
  plog_term_at b es i = None ↔
  (uint.Z i < uint.Z b.(raft.entryID.index') ∨ plog_last_index_Z b es < uint.Z i)%Z.
Proof.
  rewrite /plog_term_at /plog_last_index_Z.
  case_decide; [split; auto|]. case_decide; [split; [done|intros; lia]|].
  destruct (es !! _) eqn:Hk; simpl.
  - apply lookup_lt_Some in Hk. split; [done|intros; lia].
  - apply lookup_ge_None in Hk. split; [intros _; lia|done].
Qed.

(** A well-formed log's entry at [i] has index [i]. *)
Lemma plog_wf_lookup_index b es (k : nat) e :
  plog_wf b es → es !! k = Some e →
  (uint.Z e.(raftpb.Entry.Index') = uint.Z b.(raft.entryID.index') + S k)%Z.
Proof. intros H Hk. by apply H. Qed.

(** [plog_last] agrees with [plog_last_index_Z] on a well-formed log. *)
Lemma plog_last_index b es :
  plog_wf b es →
  (uint.Z (plog_last b es).(raft.entryID.index') = plog_last_index_Z b es)%Z.
Proof.
  intros Hwf. rewrite /plog_last /plog_last_index_Z.
  destruct (list.last es) eqn:Hl.
  - rewrite last_lookup in Hl. specialize (Hwf _ _ Hl). simpl.
    destruct es; [done|]. simpl in *. lia.
  - apply last_None in Hl. subst. simpl. lia.
Qed.

(** The term at the last index is the last entry's term. *)
Lemma plog_term_at_last b es :
  plog_wf b es →
  plog_term_at b es (plog_last b es).(raft.entryID.index')
  = Some (plog_last b es).(raft.entryID.term').
Proof.
  intros Hwf. rewrite /plog_last. destruct (list.last es) eqn:Hl.
  - rewrite last_lookup in Hl.
    eapply plog_term_at_lookup; [exact Hl|].
    specialize (Hwf _ _ Hl). destruct es; [done|]. simpl in *. lia.
  - apply plog_term_at_base.
Qed.

(** [plog_truncate_append] of a batch that continues the log is a plain
    append. *)
Lemma plog_truncate_append_cont b es ents e0 :
  ents !! 0%nat = Some e0 →
  (uint.Z e0.(raftpb.Entry.Index') = plog_last_index_Z b es + 1)%Z →
  plog_truncate_append b es ents = es ++ ents.
Proof.
  intros H0 Hidx. rewrite /plog_truncate_append. destruct ents as [|e ents']; [done|].
  simpl in H0. injection H0 as ->.
  rewrite /plog_last_index_Z in Hidx.
  replace (Z.to_nat _) with (length es) by lia.
  rewrite take_ge //.
Qed.

(** A well-formed log stays well-formed under [plog_truncate_append] of a
    well-formed batch starting inside or just after it. *)
Lemma plog_wf_truncate_append b es ents e0 :
  plog_wf b es →
  ents !! 0%nat = Some e0 →
  (uint.Z b.(raft.entryID.index') < uint.Z e0.(raftpb.Entry.Index') ≤ plog_last_index_Z b es + 1)%Z →
  (∀ (k : nat) e, ents !! k = Some e →
     (uint.Z e.(raftpb.Entry.Index') = uint.Z e0.(raftpb.Entry.Index') + k)%Z) →
  plog_wf b (plog_truncate_append b es ents).
Proof.
  intros Hwf H0 Hrange Hents. rewrite /plog_truncate_append.
  destruct ents as [|e ents']; [done|]. simpl in H0. injection H0 as ->.
  apply plog_wf_app. split; [by apply plog_wf_take|].
  intros k e' Hk. specialize (Hents _ _ Hk). simpl in Hents.
  rewrite length_take. rewrite /plog_last_index_Z in Hrange.
  rewrite Nat.min_l; [lia|lia].
Qed.
