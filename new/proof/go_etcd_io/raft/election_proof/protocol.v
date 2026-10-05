(** * Protocol-level model of etcd raft: election and log replication.

    This file is the specification side of the refinement proof in
    [New.proof.go_etcd_io.raft.election_proof.election]: it defines the abstract
    state machine that a single raft node is supposed to implement, the
    ghost state [own_raft_ghost] representing a node's protocol state, the
    knowledge [is_message] attached to a message that has legitimately been
    put on the network, and the single fancy-update lemma connecting them.

    Scope.  Everything here (and the proofs in [election.v]) assumes:
      - no pre-vote            ([r.preVote = false]),
      - no check-quorum        ([r.checkQuorum = false]),
      - no read-only requests  (no [MsgReadIndex] is ever stepped),
      - no reconfiguration     (the voter set [cfg] is fixed, no learners),
      - no snapshot received   (phase 2 of notes/raft-replication-model.md:
                                the rules [step_snap_*] and [is_message] for
                                [Snap] are here since 2026-10-02, but [Step]
                                is not yet specified for [MsgSnap]),
      - **no configuration change is ever requested** -- so the log contains
        no [EntryConfChange] or [EntryConfChangeV2] entry, and
        [r.hasUnappliedConfChanges()] is always [false].  See
        notes/raft-implementation-facts.md.

    **Since 2026-10-01 the model has a log** (notes/raft-replication-model.md):
    a node's protocol state is [(term, vote, lead, role, votes, outbox)] plus
    the log ([base], [log], [commit]) and, for a leader, each voter's
    [Progress.Match] ([matched]).  The log functions are [plog.v]'s, which
    the [raftLog] specs are stated with too.

    **Admitted.**  By the user's decision of 2026-10-01 this file may contain
    [Admitted] lemmas.  Since 2026-10-03 there are two:
    [leader_completeness] / [state_machine_safety], which are not provable
    from two nodes' ghost state (their comments say why and what a proof
    needs).  ([snap_ok_message], admitted on 2026-10-02 as a client
    [Storage] assumption, is [Qed] since [snap_ok] carries the commit bound
    and the log fact.)  Every rule's ghost update, the four protocol facts
    the code's [Panicf]s rely on, and [log_matching] are [Qed].

    The deferred premises of 2026-10-01 are all in ([app_ok]'s prefix
    clause went in on 2026-10-02 with the pinned [raftLog.entries]). *)

From RecordUpdate Require Import RecordSet.
From Perennial Require Import NamedProps.
Require Export New.proof.proof_prelude.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.
Import RecordSetNotations.

(** ** Roles *)

Module role.
Inductive t := Follower | Candidate | Leader.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End role.

(** ** Abstract messages

    One constructor per [raftpb.MessageType] raft sends between nodes.
    [Propose] is [MsgProp] ([Prop] is a keyword). *)

Module mtype.
Inductive t :=
  | Vote | VoteResp | App | AppResp | Heartbeat | HeartbeatResp
  | Propose | Snap
  | PreVote | PreVoteResp | ReadIndex | ReadIndexResp.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End mtype.

(** Every field of a [raftpb.Message] the protocol reads.  [entries] is the
    list behind [Message.Entries]; see [abs_msg] ([defs.v]) for why the
    abstraction of a physical message needs that list as an argument.

    [index]/[logterm] of a [Snap] are the snapshot's [Metadata.Index]/
    [Metadata.Term], and [voters] its [Metadata.ConfState.Voters] -- all
    behind the pointer [Message.Snapshot], read by [abs_snap] ([defs.v]).
    Every other message has [voters = []]. *)
Module msg.
Record t :=
  mk_v {
      ty : mtype.t;
      from : w64;
      to : w64;
      term : w64;
      reject : bool;
      index : w64;               (** [Index] *)
      logterm : w64;             (** [LogTerm] *)
      commit : w64;              (** [Commit] *)
      rejecthint : w64;          (** [RejectHint] *)
      entries : list raftpb.Entry.t;   (** [Entries] *)
      voters : list w64;         (** a [Snap]'s [ConfState.Voters]; [[]] otherwise *)
    }.

(** A message with no voters -- every message but a [Snap].  An
    abbreviation, not a definition: a message built with it is literally the
    constructor applied to [[]], so nothing that reduces, injects or
    rewrites a message has to unfold anything (added 2026-10-02 with the
    [voters] field, so that no user of the ten-field [msg.mk] changed). *)
Notation mk t0 fr to0 tm rj ix lt cm rh es :=
  (mk_v t0 fr to0 tm rj ix lt cm rh es []).

(** A message with no payload: every replication field zero. *)
Definition plain (ty : mtype.t) (from to term : w64) (reject : bool) : t :=
  mk ty from to term reject (W64 0) (W64 0) (W64 0) (W64 0) [].
End msg.

(** Message types whose sender claims to be the leader of [term]. *)
Definition from_leader (ty : mtype.t) : bool :=
  match ty with mtype.App | mtype.Heartbeat | mtype.Snap => true | _ => false end.

(** ** Protocol node state

    [pstate.t] is the **protocol** state of one node: what the state machine
    below and the ghost state [own_raft_ghost] are about, and nothing more.
    It is *not* the abstraction [own_raft_phys] is indexed by -- that is the
    physical abstract state [nstate.t] ([election_proof/defs.v]).  The two
    are connected by [nstate_rel] ([defs.v]); [Step]'s spec is the one place
    that crosses from one to the other.  See notes/decisions.md, "Three
    layers".

    [outbox] is the node's pending outgoing messages — the abstraction of the
    Go code's two queues, [r.msgs] and [r.msgsAfterAppend], together.

    [base]/[log]/[commit] are the log ([plog.v]): the compaction boundary,
    the entries after it, [raftLog.committed].  [matched] is each voter's
    [Progress.Match] **while the node is leader**, and [∅] otherwise (a
    non-leader's [Progress] values are left over from its last leadership
    and nothing reads them).  The field is not called [match], which is a
    keyword. *)

Module pstate.
Record t :=
  mk {
      term : w64;             (** [raft.Term] *)
      vote : w64;             (** [raft.Vote]; [W64 0] is the Go code's [None] *)
      lead : w64;             (** [raft.lead]; [W64 0] is the Go code's [None] *)
      role : role.t;          (** [raft.state] *)
      votes : gmap w64 bool;  (** [raft.trk.Votes] *)
      outbox : list msg.t;    (** [r.msgs] and [r.msgsAfterAppend], together *)
      base : raft.entryID.t;  (** the log's compaction boundary *)
      log : list raftpb.Entry.t;   (** the entries after [base] *)
      commit : w64;           (** [raftLog.committed] *)
      matched : gmap w64 w64; (** [Progress.Match] per voter, leaders only *)
    }.
#[global] Instance settable : Settable _ :=
  settable! mk <term; vote; lead; role; votes; outbox; base; log; commit; matched>.
End pstate.

(** [appendEntry]'s stamping loop: [es[k].Term = r.Term] and
    [es[k].Index = li+1+k]; nothing else about an entry changes, which is
    what keeps [Type = EntryNormal] true of the appended entries.  (Moved
    here from [defs.v] on 2026-10-01: the model's [step_win] and
    [step_propose] stamp too.) *)
Definition stamp (tm li : w64) (k : nat) (e : raftpb.Entry.t) : raftpb.Entry.t :=
  e <| raftpb.Entry.Term' := tm |>
    <| raftpb.Entry.Index' := word.add (word.add li (W64 1)) (W64 k) |>.

(** Index arithmetic for stamped entries. *)
Lemma plog_last_index_Z_nonneg b es : 0 ≤ plog_last_index_Z b es.
Proof. rewrite /plog_last_index_Z. pose proof (word.unsigned_range b.(raft.entryID.index')). lia. Qed.

Lemma stamp_index_le (L : Z) (k : nat) :
  0 ≤ L → uint.Z (word.add (word.add (W64 L) (W64 1)) (W64 (Z.of_nat k))) ≤ L + 1 + k.
Proof.
  intros HL.
  rewrite !word.unsigned_add /word.wrap.
  rewrite !word.unsigned_of_Z /word.wrap.
  set (M := 2^64).
  assert (0 < M) by (subst M; lia).
  pose proof (Z.mod_le L M HL ltac:(lia)).
  pose proof (Z.mod_pos_bound L M ltac:(lia)).
  pose proof (Z.mod_le 1 M ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound 1 M ltac:(lia)).
  pose proof (Z.mod_le (Z.of_nat k) M ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.of_nat k) M ltac:(lia)).
  pose proof (Z.mod_le (L mod M + 1 mod M) M ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound (L mod M + 1 mod M) M ltac:(lia)).
  pose proof (Z.mod_le ((L mod M + 1 mod M) mod M + Z.of_nat k mod M) M ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma leader_index_le (L : Z) :
  0 ≤ L → uint.Z (word.add (word.add (W64 L) (W64 1)) (W64 0)) ≤ L + 1.
Proof. intros HL. pose proof (stamp_index_le L 0 HL) as H. change (Z.of_nat 0) with 0%Z in H. lia. Qed.

Lemma stamp_index_eq (L : Z) (k : nat) :
  0 ≤ L → L + 1 + k < 2^64 →
  uint.Z (word.add (word.add (W64 L) (W64 1)) (W64 (Z.of_nat k))) = L + 1 + k.
Proof. intros. word. Qed.

(** What a receiver of an [App] needs of its batch ([raftLog.maybeAppend]'s
    premises): consecutive indices from [index + 1], no wrap, no conf
    change (phase-1 scope). *)
Definition app_payload_ok (m : msg.t) : Prop :=
  plog_wf (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries) ∧
  uint.Z m.(msg.index) + Z.of_nat (length m.(msg.entries)) + 1 < 2 ^ 64 ∧
  Forall (λ e, e.(raftpb.Entry.Type') = W32 0) m.(msg.entries).

(** A prefix of a well-formed, no-wrap, conf-change-free log from [i + 1]
    on is a batch [app_payload_ok] accepts at [(t, i)]. *)
Lemma app_payload_from_log (b : raft.entryID.t) (L : list raftpb.Entry.t) (t i : w64)
    (es : list raftpb.Entry.t) :
  plog_wf b L →
  uint.Z b.(raft.entryID.index') + Z.of_nat (length L) + 1 < 2 ^ 64 →
  uint.Z b.(raft.entryID.index') ≤ uint.Z i ≤ plog_last_index_Z b L →
  Forall (λ e, e.(raftpb.Entry.Type') = W32 0) L →
  es `prefix_of` plog_from b L (word.add i (W64 1)) →
  plog_wf (raft.entryID.mk t i) es ∧
  uint.Z i + Z.of_nat (length es) + 1 < 2 ^ 64 ∧
  Forall (λ e, e.(raftpb.Entry.Type') = W32 0) es.
Proof.
  intros Hwf Hnw Hi HN Hpre.
  rewrite /plog_last_index_Z in Hi.
  rewrite /plog_from in Hpre.
  replace (Z.to_nat (uint.Z (word.add i (W64 1)) - uint.Z b.(raft.entryID.index') - 1))
    with (Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index'))) in Hpre by word.
  set (k := Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index'))) in *.
  pose proof (prefix_length _ _ Hpre) as Hlen. rewrite length_drop in Hlen.
  split_and!.
  - intros j e Hj. simpl.
    pose proof (prefix_lookup_Some _ _ _ _ Hj Hpre) as Hj'.
    rewrite lookup_drop in Hj'. specialize (Hwf _ _ Hj'). lia.
  - lia.
  - rewrite List.Forall_forall in HN. apply List.Forall_forall. intros e He. apply HN.
    apply list_elem_of_In. rewrite -(take_drop k L) elem_of_app. right.
    apply (elem_of_prefix es); [by apply list_elem_of_In|exact Hpre].
Qed.

(** The entry at index [i] of a log, if it is in the stored suffix. *)
Definition plog_entry_at (b : raft.entryID.t) (es : list raftpb.Entry.t) (i : w64)
  : option raftpb.Entry.t :=
  if decide (uint.Z i ≤ uint.Z b.(raft.entryID.index')) then None
  else es !! Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index') - 1).


(** [plog_find_conflict] returns the index of the first entry that does
    not match, all before it matching. *)
Lemma plog_find_conflict_some b es ents :
  plog_find_conflict b es ents ≠ W64 0 →
  ∃ (d : nat) e, ents !! d = Some e ∧
    e.(raftpb.Entry.Index') = plog_find_conflict b es ents ∧
    ¬ plog_matches b es (ent_id e) ∧
    (∀ (j : nat) e', (j < d)%nat → ents !! j = Some e' → plog_matches b es (ent_id e')).
Proof.
  induction ents as [|a ents IH]; simpl; [done|].
  case_decide as Ha.
  - intros Hne. destruct (IH Hne) as (d & e & Hd & He & Hnm & Hbefore).
    exists (S d), e. split_and!; [done|done|done|].
    intros [|j] e' Hj Hj'; simpl in Hj'.
    + by injection Hj' as <-.
    + apply (Hbefore j); [lia|done].
  - intros _. exists 0%nat, a. split_and!; [done|done|done|]. intros j e' Hj. lia.
Qed.

(** ... and [0] when every entry matches, provided no entry has index
    [0]. *)
Lemma plog_find_conflict_zero b es ents :
  (∀ (k : nat) e, ents !! k = Some e → e.(raftpb.Entry.Index') ≠ W64 0) →
  plog_find_conflict b es ents = W64 0 →
  ∀ (k : nat) e, ents !! k = Some e → plog_matches b es (ent_id e).
Proof.
  induction ents as [|a ents IH]; simpl; intros Hnz Hci k e Hk; [done|].
  case_decide as Ha.
  - destruct k as [|k]; simpl in Hk; [by injection Hk as <-|].
    apply (IH (λ k e H, Hnz (S k) e H) Hci k e Hk).
  - exfalso. apply (Hnz 0%nat a); done.
Qed.

(** After [plog_maybe_append] of a well-formed, non-wrapping batch, the
    log reaches [lastnewi]: the batch's entries are all there (no
    conflict), or the log was cut at the first conflict and the rest of
    the batch appended. *)
Lemma plog_maybe_append_last b es (prev : raft.entryID.t) ents lastnewi es' :
  plog_wf prev ents →
  uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1 < 2 ^ 64 →
  plog_maybe_append b es prev ents = Some (lastnewi, es') →
  uint.Z lastnewi ≤ plog_last_index_Z b es'.
Proof.
  intros Hwf Hnw. rewrite /plog_maybe_append. case_decide as Hm; [|done].
  intros [= <- <-].
  rewrite word.unsigned_of_Z_nowrap; [|pose proof (word.unsigned_range prev.(raft.entryID.index')); lia].
  pose proof (plog_term_at_Some_range _ _ _ _ Hm) as [Hb Hl].
  assert (Hnz : ∀ (k : nat) e, ents !! k = Some e → e.(raftpb.Entry.Index') ≠ W64 0).
  { intros k e Hk Hz. specialize (Hwf _ _ Hk). rewrite Hz in Hwf.
    change (uint.Z (W64 0)) with 0 in Hwf.
    pose proof (word.unsigned_range prev.(raft.entryID.index')). lia. }
  case_decide as Hci.
  - (* no conflict: the last entry of the batch is in the log *)
    destruct (decide (length ents = 0%nat)) as [H0|H0]; [lia|].
    destruct (lookup_lt_is_Some_2 ents (length ents - 1)%nat ltac:(lia)) as [e He].
    pose proof (plog_find_conflict_zero _ _ _ Hnz Hci _ _ He) as Hme.
    rewrite /plog_matches /ent_id /= in Hme.
    pose proof (plog_term_at_Some_range _ _ _ _ Hme) as [_ Hle].
    specialize (Hwf _ _ He). simpl in Hwf. lia.
  - (* a conflict at batch position [d]: cut there, append the rest *)
    destruct (plog_find_conflict_some _ _ _ Hci) as (d & e & Hd & Hei & _ & Hbefore).
    pose proof (Hwf _ _ Hd) as Hed. simpl in Hed.
    set (ci := plog_find_conflict b es ents) in *.
    assert (Hdrop : Z.to_nat (uint.Z ci - uint.Z prev.(raft.entryID.index') - 1) = d) by
      (rewrite -Hei; lia).
    rewrite Hdrop (drop_S _ _ _ Hd).
    (* the conflicting entry is at most one past the log's end *)
    assert (Hend : uint.Z e.(raftpb.Entry.Index') ≤ plog_last_index_Z b es + 1).
    { destruct d as [|d']; [lia|].
      destruct (lookup_lt_is_Some_2 ents d' ltac:(apply lookup_lt_Some in Hd; lia)) as [e' He'].
      pose proof (Hbefore d' e' ltac:(lia) He') as Hme'.
      rewrite /plog_matches /ent_id /= in Hme'.
      pose proof (plog_term_at_Some_range _ _ _ _ Hme') as [_ Hle].
      pose proof (Hwf _ _ He') as Hed'. simpl in Hed'. lia. }
    rewrite /plog_truncate_append /plog_last_index_Z length_app length_take /=.
    rewrite length_drop.
    apply lookup_lt_Some in Hd.
    rewrite /plog_last_index_Z in Hend Hl.
    lia.
Qed.


(** ** Pure facts the replication-safety invariants rest on (2026-10-02)

    See [log_ok], [log_recs] and [ack_agree] in the ghost section. *)

(** Well-formedness *in range*: an entry whose position puts it at an index
    a [w64] can name has that index.  This is [plog_wf] minus the entries
    past [2^64 - 1], which only [step_win] can create (its stamped entry
    wraps when [lastIndex() = 2^64 - 1]; the rule has no no-wrap premise,
    and the code's [Hnowrap] is not in [pstate]).  [plog_term_at] never
    reaches those positions, so nothing below needs more. *)
Definition plog_wf_r (b : raft.entryID.t) (es : list raftpb.Entry.t) : Prop :=
  ∀ (k : nat) e, es !! k = Some e →
    uint.Z b.(raft.entryID.index') + Z.of_nat k + 1 < 2 ^ 64 →
    uint.Z e.(raftpb.Entry.Index') = uint.Z b.(raft.entryID.index') + Z.of_nat k + 1.

Lemma plog_wf_wf_r b es : plog_wf b es → plog_wf_r b es.
Proof. intros H k e Hk _. specialize (H k e Hk). lia. Qed.

(** The index just before position [k] of the suffix: where the [k]-th
    entry's predecessor is. *)
Definition pidx (b : raft.entryID.t) (k : nat) : w64 :=
  W64 (uint.Z b.(raft.entryID.index') + Z.of_nat k).

Lemma plog_term_at_app_l b es es2 (j : w64) :
  uint.Z j ≤ plog_last_index_Z b es →
  plog_term_at b (es ++ es2) j = plog_term_at b es j.
Proof.
  rewrite /plog_term_at /plog_last_index_Z. intros Hj.
  case_decide; [done|]. case_decide; [done|].
  rewrite lookup_app_l //. lia.
Qed.

Lemma plog_term_at_app_r b es es2 (j : w64) :
  plog_last_index_Z b es < uint.Z j →
  plog_term_at b (es ++ es2) j =
  (λ e, e.(raftpb.Entry.Term')) <$>
    es2 !! Z.to_nat (uint.Z j - plog_last_index_Z b es - 1).
Proof.
  rewrite /plog_term_at /plog_last_index_Z. intros Hj.
  rewrite decide_False; [|lia]. rewrite decide_False; [|lia].
  rewrite lookup_app_r; [|lia].
  by replace (Z.to_nat (uint.Z j - uint.Z b.(raft.entryID.index') - 1) - length es)%nat
    with (Z.to_nat (uint.Z j - (uint.Z b.(raft.entryID.index') + Z.of_nat (length es)) - 1))
    by lia.
Qed.

Lemma plog_term_at_take b es (n : nat) (j : w64) :
  uint.Z j ≤ uint.Z b.(raft.entryID.index') + n →
  plog_term_at b (take n es) j = plog_term_at b es j.
Proof.
  rewrite /plog_term_at. intros Hj.
  case_decide; [done|]. case_decide; [done|].
  rewrite lookup_take_lt //. lia.
Qed.

Lemma plog_term_at_in_range b es (j : w64) :
  uint.Z b.(raft.entryID.index') ≤ uint.Z j ≤ plog_last_index_Z b es →
  is_Some (plog_term_at b es j).
Proof.
  intros Hj. destruct (plog_term_at b es j) eqn:H; [by eexists|].
  apply plog_term_at_None_range in H. lia.
Qed.

(** Above the base, a term is an entry's, and (in range) the entry is at
    the right index. *)
Lemma plog_term_at_Some_entry b es (j t : w64) :
  plog_wf_r b es → plog_term_at b es j = Some t →
  uint.Z b.(raft.entryID.index') < uint.Z j →
  ∃ e, es !! Z.to_nat (uint.Z j - uint.Z b.(raft.entryID.index') - 1) = Some e ∧
       e.(raftpb.Entry.Index') = j ∧ e.(raftpb.Entry.Term') = t.
Proof.
  intros Hwf Ht Hb. rewrite /plog_term_at in Ht.
  rewrite decide_False in Ht; [|lia]. rewrite decide_False in Ht; [|lia].
  destruct (es !! _) as [e|] eqn:He; [|done]. simpl in Ht. injection Ht as <-.
  exists e. split_and!; [done| |done].
  pose proof (word.unsigned_range j).
  specialize (Hwf _ _ He ltac:(lia)). apply word.unsigned_inj. lia.
Qed.

Lemma plog_entry_at_lookup b es (j : w64) :
  uint.Z b.(raft.entryID.index') < uint.Z j →
  plog_entry_at b es j = es !! Z.to_nat (uint.Z j - uint.Z b.(raft.entryID.index') - 1).
Proof. intros Hj. rewrite /plog_entry_at decide_False //. lia. Qed.

(** The last entry's term, in range. *)
Lemma plog_term_at_last_r b es :
  plog_wf_r b es → plog_last_index_Z b es < 2 ^ 64 →
  plog_term_at b es (W64 (plog_last_index_Z b es))
  = Some (plog_last b es).(raft.entryID.term').
Proof.
  intros Hwf Hlt. pose proof (plog_last_index_Z_nonneg b es) as H0.
  rewrite /plog_last. destruct (list.last es) as [e|] eqn:Hl.
  - rewrite last_lookup in Hl.
    destruct es as [|x es']; [done|].
    eapply plog_term_at_lookup; [exact Hl|].
    rewrite /plog_last_index_Z in Hlt H0 |- *. simpl in *.
    rewrite word.unsigned_of_Z_nowrap; lia.
  - apply last_None in Hl. subst.
    rewrite /plog_last_index_Z /= Z.add_0_r.
    replace (W64 (uint.Z b.(raft.entryID.index'))) with b.(raft.entryID.index')
      by (apply word.unsigned_inj; rewrite word.unsigned_of_Z_nowrap; [done|word]).
    apply plog_term_at_base.
Qed.

(** What two logs' records give: entries at the same (term, index) are the
    same entry and have the same predecessor term.  [log_recs_agree] derives
    it from the ghost state. *)
Definition recs_agree (b1 : raft.entryID.t) (es1 : list raftpb.Entry.t)
    (b2 : raft.entryID.t) (es2 : list raftpb.Entry.t) : Prop :=
  ∀ (k1 k2 : nat) e1 e2, es1 !! k1 = Some e1 → es2 !! k2 = Some e2 →
    uint.Z b1.(raft.entryID.index') + Z.of_nat k1 + 1 < 2 ^ 64 →
    uint.Z b2.(raft.entryID.index') + Z.of_nat k2 + 1 < 2 ^ 64 →
    e1.(raftpb.Entry.Term') = e2.(raftpb.Entry.Term') →
    e1.(raftpb.Entry.Index') = e2.(raftpb.Entry.Index') →
    e1 = e2 ∧ plog_term_at b1 es1 (pidx b1 k1) = plog_term_at b2 es2 (pidx b2 k2).

(** Log matching, pure: two logs with the same term at [i] have the same
    terms all the way down to the higher of their bases. *)
Lemma plog_match_down b1 es1 b2 es2 (i : w64) :
  plog_wf_r b1 es1 → plog_wf_r b2 es2 → recs_agree b1 es1 b2 es2 →
  is_Some (plog_term_at b1 es1 i) →
  plog_term_at b1 es1 i = plog_term_at b2 es2 i →
  ∀ j : w64, uint.Z b1.(raft.entryID.index') ≤ uint.Z j →
    uint.Z b2.(raft.entryID.index') ≤ uint.Z j → uint.Z j ≤ uint.Z i →
    plog_term_at b1 es1 j = plog_term_at b2 es2 j.
Proof.
  intros Hwf1 Hwf2 HRA Hs Heq j Hj1 Hj2 Hji.
  remember (Z.to_nat (uint.Z i - uint.Z j)) as n eqn:Hn.
  revert i Hs Heq Hji Hn. induction n as [|n IH]; intros i Hs Heq Hji Hn.
  - assert (i = j) as <- by (apply word.unsigned_inj; lia). done.
  - destruct Hs as [t Ht].
    pose proof (word.unsigned_range i). pose proof (word.unsigned_range j).
    assert (Hi1 : uint.Z b1.(raft.entryID.index') < uint.Z i) by lia.
    assert (Hi2 : uint.Z b2.(raft.entryID.index') < uint.Z i) by lia.
    destruct (plog_term_at_Some_entry _ _ _ _ Hwf1 Ht Hi1) as (e1 & He1 & Hidx1 & Ht1).
    assert (Ht' : plog_term_at b2 es2 i = Some t) by (rewrite -Heq //).
    destruct (plog_term_at_Some_entry _ _ _ _ Hwf2 Ht' Hi2) as (e2 & He2 & Hidx2 & Ht2).
    destruct (HRA _ _ _ _ He1 He2 ltac:(lia) ltac:(lia) ltac:(congruence) ltac:(congruence))
      as [_ Hpt].
    set (i' := W64 (uint.Z i - 1)).
    assert (Hi' : uint.Z i' = uint.Z i - 1) by (subst i'; word).
    assert (Hp1 : pidx b1 (Z.to_nat (uint.Z i - uint.Z b1.(raft.entryID.index') - 1)) = i')
      by (rewrite /pidx /i'; f_equal; lia).
    assert (Hp2 : pidx b2 (Z.to_nat (uint.Z i - uint.Z b2.(raft.entryID.index') - 1)) = i')
      by (rewrite /pidx /i'; f_equal; lia).
    rewrite Hp1 Hp2 in Hpt.
    apply (IH i'); [| exact Hpt | lia | lia].
    apply plog_term_at_in_range.
    pose proof (plog_term_at_Some_range _ _ _ _ Ht). lia.
Qed.

(** A batch [ents] after [prev], taken from a log [l] (a prefix of [l]'s
    entries after [prev], which [l] has), agrees with [l] in terms on
    [[prev.index, prev.index + |ents|]]. *)
Lemma plog_prefix_batch (bL : raft.entryID.t) l (prev : raft.entryID.t) ents :
  uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1 < 2 ^ 64 →
  plog_term_at bL l prev.(raft.entryID.index') = Some prev.(raft.entryID.term') →
  ents `prefix_of` plog_from bL l (word.add prev.(raft.entryID.index') (W64 1)) →
  ∀ j : w64, uint.Z prev.(raft.entryID.index') ≤ uint.Z j ≤
             uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) →
    plog_term_at bL l j = plog_term_at prev ents j.
Proof.
  intros Hnw Hprev Hpre j Hj.
  pose proof (plog_term_at_Some_range _ _ _ _ Hprev) as [Hb _].
  destruct (decide (uint.Z j = uint.Z prev.(raft.entryID.index'))) as [Heq|Hne].
  { assert (j = prev.(raft.entryID.index')) as -> by (apply word.unsigned_inj; lia).
    rewrite Hprev plog_term_at_base //. }
  set (p := Z.to_nat (uint.Z j - uint.Z prev.(raft.entryID.index') - 1)).
  destruct (lookup_lt_is_Some_2 ents p ltac:(lia)) as [x Hx].
  pose proof (prefix_lookup_Some _ _ _ _ Hx Hpre) as Hx'.
  rewrite /plog_from lookup_drop in Hx'.
  assert (Hadd : uint.Z (word.add prev.(raft.entryID.index') (W64 1))
                 = uint.Z prev.(raft.entryID.index') + 1) by word.
  rewrite (plog_term_at_lookup prev ents j p x Hx); [|lia].
  erewrite plog_term_at_lookup; [done|exact Hx'|]. lia.
Qed.

(** [plog_maybe_append], taken apart: the previous entry matched, the new
    last index is the batch's, and either nothing changed (every entry
    matched) or the log was cut at the first conflicting entry [ents[d]]
    and the batch from [d] on appended. *)
Lemma plog_maybe_append_inv b es (prev : raft.entryID.t) ents lastnewi es' :
  plog_wf prev ents →
  uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1 < 2 ^ 64 →
  plog_maybe_append b es prev ents = Some (lastnewi, es') →
  plog_matches b es prev ∧
  uint.Z lastnewi = uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) ∧
  ( (es' = es ∧ ∀ (k : nat) e, ents !! k = Some e → plog_matches b es (ent_id e))
  ∨ (∃ (d : nat) e, ents !! d = Some e ∧ ¬ plog_matches b es (ent_id e) ∧
       (∀ (k : nat) e', (k < d)%nat → ents !! k = Some e' → plog_matches b es (ent_id e')) ∧
       uint.Z e.(raftpb.Entry.Index') = uint.Z prev.(raft.entryID.index') + Z.of_nat d + 1 ∧
       uint.Z e.(raftpb.Entry.Index') ≤ plog_last_index_Z b es + 1 ∧
       es' = take (Z.to_nat (uint.Z e.(raftpb.Entry.Index') - uint.Z b.(raft.entryID.index') - 1)) es
             ++ drop d ents) ).
Proof.
  intros Hwf Hnw. rewrite /plog_maybe_append. case_decide as Hm; [|done].
  intros [= <- <-]. split; [done|].
  split. { rewrite word.unsigned_of_Z_nowrap; [done|].
           pose proof (word.unsigned_range prev.(raft.entryID.index')). lia. }
  pose proof (plog_term_at_Some_range _ _ _ _ Hm) as [Hb Hl].
  assert (Hnz : ∀ (k : nat) e, ents !! k = Some e → e.(raftpb.Entry.Index') ≠ W64 0).
  { intros k e Hk Hz. specialize (Hwf _ _ Hk). rewrite Hz in Hwf.
    change (uint.Z (W64 0)) with 0 in Hwf.
    pose proof (word.unsigned_range prev.(raft.entryID.index')). lia. }
  case_decide as Hci.
  - left. split; [done|]. by apply plog_find_conflict_zero.
  - right. destruct (plog_find_conflict_some _ _ _ Hci) as (d & e & Hd & Hei & Hnm & Hbefore).
    pose proof (Hwf _ _ Hd) as Hed. simpl in Hed.
    exists d, e. split_and!; [done|done|done|lia| |].
    + destruct d as [|d']; [rewrite /plog_last_index_Z in Hl |- *; lia|].
      destruct (lookup_lt_is_Some_2 ents d' ltac:(apply lookup_lt_Some in Hd; lia)) as [e' He'].
      pose proof (Hbefore d' e' ltac:(lia) He') as Hme'.
      rewrite /plog_matches /ent_id /= in Hme'.
      pose proof (plog_term_at_Some_range _ _ _ _ Hme') as [_ Hle].
      pose proof (Hwf _ _ He') as Hed'. simpl in Hed'. lia.
    + rewrite -Hei.
      replace (Z.to_nat (uint.Z e.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1))
        with d by lia.
      rewrite (drop_S _ _ _ Hd) /plog_truncate_append. done.
Qed.

(** The batch's entries, by index. *)
Lemma batch_lookup (prev : raft.entryID.t) ents (j : w64) :
  plog_wf prev ents →
  uint.Z prev.(raft.entryID.index') < uint.Z j ≤
    uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) →
  ∃ x, ents !! Z.to_nat (uint.Z j - uint.Z prev.(raft.entryID.index') - 1) = Some x ∧
       x.(raftpb.Entry.Index') = j ∧
       plog_term_at prev ents j = Some x.(raftpb.Entry.Term').
Proof.
  intros Hwf Hj.
  destruct (lookup_lt_is_Some_2 ents (Z.to_nat (uint.Z j - uint.Z prev.(raft.entryID.index') - 1))
              ltac:(lia)) as [x Hx].
  exists x. split_and!; [done| |].
  - specialize (Hwf _ _ Hx). apply word.unsigned_inj. lia.
  - eapply plog_term_at_lookup; [exact Hx|lia].
Qed.

(** After [plog_maybe_append], the log has the batch's terms on
    [[prev.index, prev.index + |ents|]]. *)
Lemma plog_maybe_append_batch b es (prev : raft.entryID.t) ents lastnewi es' :
  plog_wf prev ents →
  uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1 < 2 ^ 64 →
  plog_maybe_append b es prev ents = Some (lastnewi, es') →
  ∀ j : w64, uint.Z prev.(raft.entryID.index') ≤ uint.Z j ≤
             uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) →
    plog_term_at b es' j = plog_term_at prev ents j.
Proof.
  intros Hwf Hnw Happ j Hj.
  destruct (plog_maybe_append_inv _ _ _ _ _ _ Hwf Hnw Happ) as (Hm & Hli & Hcase).
  pose proof (plog_term_at_Some_range _ _ _ _ Hm) as [Hb Hl].
  (* below the conflict (or everywhere, without one), the old log has the
     batch's terms *)
  assert (Hold : ∀ (d : nat), (∀ (k : nat) e', (k < d)%nat → ents !! k = Some e' →
                                 plog_matches b es (ent_id e')) →
                 uint.Z j ≤ uint.Z prev.(raft.entryID.index') + d →
                 plog_term_at b es j = plog_term_at prev ents j).
  { intros d Hbef Hjd.
    destruct (decide (uint.Z j = uint.Z prev.(raft.entryID.index'))) as [Heq|Hne].
    - assert (j = prev.(raft.entryID.index')) as -> by (apply word.unsigned_inj; lia).
      rewrite plog_term_at_base. exact Hm.
    - destruct (batch_lookup prev ents j Hwf ltac:(lia)) as (x & Hx & Hxi & Hxt).
      rewrite Hxt. unshelve epose proof (Hbef _ x _ Hx) as Hmx; [lia|].
      rewrite /plog_matches /ent_id /= Hxi in Hmx. exact Hmx. }
  destruct Hcase as [[-> Hall] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & ->)].
  - apply (Hold (length ents)); [|lia].
    intros k e' _ Hk. by apply (Hall k).
  - set (n := Z.to_nat (uint.Z e.(raftpb.Entry.Index') - uint.Z b.(raft.entryID.index') - 1)).
    assert (Hn : (n ≤ length es)%nat) by (rewrite /plog_last_index_Z in Hend; lia).
    assert (Hlt : plog_last_index_Z b (take n es)
                  = uint.Z e.(raftpb.Entry.Index') - 1).
    { rewrite /plog_last_index_Z length_take. lia. }
    destruct (decide (uint.Z j < uint.Z e.(raftpb.Entry.Index'))) as [Hjc|Hjc].
    + rewrite plog_term_at_app_l; [|lia].
      rewrite plog_term_at_take; [|lia].
      apply (Hold d); [exact Hbefore|lia].
    + rewrite plog_term_at_app_r; [|lia]. rewrite Hlt lookup_drop.
      destruct (batch_lookup prev ents j Hwf ltac:(lia)) as (x & Hx & _ & Hxt).
      rewrite Hxt.
      replace (d + Z.to_nat (uint.Z j - (uint.Z e.(raftpb.Entry.Index') - 1) - 1))%nat
        with (Z.to_nat (uint.Z j - uint.Z prev.(raft.entryID.index') - 1)) by lia.
      rewrite Hx //.
Qed.

(** Below the cut the log is unchanged. *)
Lemma plog_cut_keep b es (ci : Z) ents2 (j : w64) :
  uint.Z b.(raft.entryID.index') < ci ≤ plog_last_index_Z b es + 1 →
  uint.Z j < ci →
  plog_term_at b (take (Z.to_nat (ci - uint.Z b.(raft.entryID.index') - 1)) es ++ ents2) j
  = plog_term_at b es j.
Proof.
  intros Hci Hj.
  rewrite plog_term_at_app_l; last first.
  { rewrite /plog_last_index_Z length_take. rewrite /plog_last_index_Z in Hci. lia. }
  rewrite plog_term_at_take //. lia.
Qed.

Lemma plog_cut_last b es (ci : Z) (ents2 : list raftpb.Entry.t) :
  uint.Z b.(raft.entryID.index') < ci ≤ plog_last_index_Z b es + 1 →
  plog_last_index_Z b (take (Z.to_nat (ci - uint.Z b.(raft.entryID.index') - 1)) es ++ ents2)
  = ci - 1 + Z.of_nat (length ents2).
Proof.
  intros Hci. rewrite /plog_last_index_Z length_app length_take.
  rewrite /plog_last_index_Z in Hci. lia.
Qed.

(** [plog_maybe_append] keeps the log well-formed (in range), and the new
    log reaches [lastnewi] -- exactly, when it was cut. *)
Lemma plog_maybe_append_wf_r b es (prev : raft.entryID.t) ents lastnewi es' :
  plog_wf_r b es →
  plog_wf prev ents →
  uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1 < 2 ^ 64 →
  plog_maybe_append b es prev ents = Some (lastnewi, es') →
  plog_wf_r b es' ∧
  uint.Z lastnewi ≤ plog_last_index_Z b es'.
Proof.
  intros Hwfr Hwf Hnw Happ.
  pose proof (plog_maybe_append_last _ _ _ _ _ _ Hwf Hnw Happ) as Hlast.
  destruct (plog_maybe_append_inv _ _ _ _ _ _ Hwf Hnw Happ) as (Hm & Hli & Hcase).
  pose proof (plog_term_at_Some_range _ _ _ _ Hm) as [Hb Hl].
  destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & ->)];
    [split; done|].
  set (n := Z.to_nat (uint.Z e.(raftpb.Entry.Index') - uint.Z b.(raft.entryID.index') - 1)).
  assert (Hn : (n ≤ length es)%nat) by (rewrite /plog_last_index_Z in Hend; lia).
  split; [|done].
  intros k x Hk Hr.
  destruct (decide (k < n)%nat) as [Hkn|Hkn].
  - rewrite lookup_app_l in Hk; [|rewrite length_take; lia].
    rewrite lookup_take_lt in Hk; [|done]. by apply Hwfr.
  - rewrite lookup_app_r in Hk; [|rewrite length_take; lia].
    rewrite length_take lookup_drop in Hk.
    specialize (Hwf _ _ Hk). simpl in Hwf. lia.
Qed.

(** ** Full logs (2026-10-03)

    Leader Completeness compares logs *below* their compaction boundaries:
    a voter's log at vote time against a candidate's, a follower's after a
    snapshot against the leader's.  The ghost state therefore keeps, for
    each log [(b, es)], the compacted prefix [fp] (entries [1 .. b.index],
    the last one [b]) with its records, and reasons about the **full log**
    [fp ++ es] from the fixed base [base0].  [full_ok] is the link; the
    lemmas below translate [plog_term_at]/[plog_last] between the two
    views.  ([plog_wf base0 F] already puts every entry of a full log at a
    [w64] index: nothing in it has wrapped.) *)

Definition base0 : raft.entryID.t := raft.entryID.mk (W64 0) (W64 0).

Definition full_ok (b : raft.entryID.t) (fp : list raftpb.Entry.t) : Prop :=
  Z.of_nat (length fp) = uint.Z b.(raft.entryID.index') ∧
  plog_wf base0 fp ∧ plog_last base0 fp = b.

Lemma base0_index : uint.Z base0.(raft.entryID.index') = 0.
Proof. done. Qed.

Lemma full_ok_base0 : full_ok base0 [].
Proof. split_and!; [done| by intros ?? | done]. Qed.

Lemma full_term_at b fp es (j : w64) :
  full_ok b fp → uint.Z b.(raft.entryID.index') ≤ uint.Z j →
  plog_term_at base0 (fp ++ es) j = plog_term_at b es j.
Proof.
  intros (Hlen & Hwf & Hlast) Hj.
  rewrite /plog_term_at base0_index.
  repeat case_decide; try lia.
  - (* the empty prefix: [b = base0] *)
    assert (fp = []) as -> by (apply nil_length_inv; lia).
    rewrite /plog_last /= in Hlast. subst b. done.
  - rewrite lookup_app_l; [|lia].
    rewrite /plog_last in Hlast.
    destruct (list.last fp) as [x|] eqn:Hx.
    + rewrite last_lookup in Hx.
      replace (Z.to_nat (uint.Z j - 0 - 1)) with (pred (length fp)) by lia.
      rewrite Hx /=. subst b. done.
    + apply last_None in Hx. subst fp. simpl in Hlen. lia.
  - rewrite lookup_app_r; [|lia]. do 2 f_equal. lia.
Qed.

Lemma full_term_at_le b fp es (j : w64) :
  full_ok b fp → uint.Z j ≤ uint.Z b.(raft.entryID.index') →
  plog_term_at base0 (fp ++ es) j = plog_term_at base0 fp j.
Proof.
  intros (Hlen & _ & _) Hj. apply plog_term_at_app_l.
  rewrite /plog_last_index_Z base0_index. lia.
Qed.

Lemma full_last b fp es :
  full_ok b fp → plog_last base0 (fp ++ es) = plog_last b es.
Proof.
  intros (_ & _ & Hlast). rewrite /plog_last last_app.
  destruct (list.last es); [done|]. exact Hlast.
Qed.

Lemma full_last_index b fp es :
  full_ok b fp → plog_last_index_Z base0 (fp ++ es) = plog_last_index_Z b es.
Proof.
  intros (Hlen & _ & _). rewrite /plog_last_index_Z base0_index length_app. lia.
Qed.

Lemma full_up_to_date b fp es x :
  full_ok b fp → plog_up_to_date base0 (fp ++ es) x = plog_up_to_date b es x.
Proof. intros H. rewrite /plog_up_to_date (full_last _ _ _ H) //. Qed.

Lemma full_wf b fp es :
  full_ok b fp → plog_wf b es → plog_wf base0 (fp ++ es).
Proof.
  intros (Hlen & Hwf & _) Hwfe. apply plog_wf_app. split; [done|].
  intros k e Hk. specialize (Hwfe k e Hk). rewrite base0_index. lia.
Qed.

(** In range, [plog_wf_r] is [plog_wf]. *)
Lemma plog_wf_r_wf b es :
  plog_wf_r b es → plog_last_index_Z b es < 2 ^ 64 → plog_wf b es.
Proof.
  intros Hwf Hr k e Hk. apply lookup_lt_Some in Hk as Hlt.
  specialize (Hwf k e Hk). rewrite /plog_last_index_Z in Hr. lia.
Qed.

(** ... and a [plog_wf] log is in range. *)
Lemma plog_wf_range b es :
  plog_wf b es → plog_last_index_Z b es < 2 ^ 64.
Proof.
  intros Hwf. rewrite /plog_last_index_Z.
  destruct (decide (length es = 0%nat)) as [H0|H0].
  { rewrite H0. pose proof (word.unsigned_range b.(raft.entryID.index')). lia. }
  destruct (lookup_lt_is_Some_2 es (pred (length es)) ltac:(lia)) as [e He].
  specialize (Hwf _ _ He). pose proof (word.unsigned_range e.(raftpb.Entry.Index')). lia.
Qed.

(** The prefix of a full log up to [i], as the compacted prefix of the
    log with base [(t, i)]. *)
Lemma full_ok_take F (t i : w64) :
  plog_wf base0 F → plog_term_at base0 F i = Some t →
  full_ok (raft.entryID.mk t i) (take (Z.to_nat (uint.Z i)) F).
Proof.
  intros Hwf Ht.
  pose proof (plog_term_at_Some_range _ _ _ _ Ht) as [_ Hle].
  rewrite /plog_last_index_Z base0_index in Hle.
  pose proof (word.unsigned_range i).
  split_and!.
  - rewrite length_take /= Nat.min_l; lia.
  - by apply plog_wf_take.
  - rewrite /plog_last.
    destruct (decide (uint.Z i = 0)) as [H0|H0].
    + rewrite /plog_term_at base0_index decide_False in Ht; [|lia].
      rewrite decide_True in Ht; [|lia]. injection Ht as <-.
      replace (Z.to_nat (uint.Z i)) with 0%nat by lia. simpl.
      rewrite /base0. f_equal. word.
    + rewrite last_lookup length_take.
      replace (pred (Z.to_nat (uint.Z i) `min` length F)) with (Z.to_nat (uint.Z i - 0 - 1)) by lia.
      rewrite lookup_take_lt; [|lia].
      rewrite /plog_term_at base0_index decide_False in Ht; [|lia].
      rewrite decide_False in Ht; [|lia].
      destruct (F !! _) as [x|] eqn:Hx; [|done]. simpl in Ht. injection Ht as <-.
      rewrite /ent_id. f_equal.
      specialize (Hwf _ _ Hx). rewrite base0_index in Hwf. word.
Qed.

Lemma plog_term_at_take_full F (n : nat) (j : w64) :
  uint.Z j ≤ n → plog_term_at base0 (take n F) j = plog_term_at base0 F j.
Proof. intros Hj. apply plog_term_at_take. rewrite base0_index. lia. Qed.

(** A full log is defined everywhere up to its end. *)
Lemma full_term_at_some F (j k : w64) :
  is_Some (plog_term_at base0 F k) → uint.Z j ≤ uint.Z k →
  is_Some (plog_term_at base0 F j).
Proof.
  intros [x Hx] Hjk. apply plog_term_at_in_range.
  pose proof (plog_term_at_Some_range _ _ _ _ Hx). rewrite base0_index. word.
Qed.

(** Prefixes keep the terms they have. *)
Lemma plog_term_at_prefix b F0 F (j : w64) :
  F0 `prefix_of` F → is_Some (plog_term_at b F0 j) →
  plog_term_at b F j = plog_term_at b F0 j.
Proof.
  intros [F' ->] [x Hx]. apply plog_term_at_app_l.
  by pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ ?].
Qed.


(** The pure side of a campaign record ([is_camp], 2026-10-03): a
    well-formed full log all of whose terms are below the campaign's. *)
Definition camp_ok (T : w64) (F : list raftpb.Entry.t) : Prop :=
  plog_wf base0 F ∧
  ∀ (j x : w64), plog_term_at base0 F j = Some x → uint.Z x < uint.Z T.

(** What an entry's record says of its predecessor term [pt] ([is_entry_r]):
    the entry, at index [k], is past the leader's campaign log [F0]; it
    follows [F0]'s last entry or one of its own term; [pt ≤ T]. *)
Definition pt_ok (F0 : list raftpb.Entry.t) (T : w64) (k : Z) (pt : w64) : Prop :=
  plog_last_index_Z base0 F0 < k ∧ uint.Z pt ≤ uint.Z T ∧
  (k = plog_last_index_Z base0 F0 + 1 → pt = (plog_last base0 F0).(raft.entryID.term')) ∧
  (plog_last_index_Z base0 F0 + 1 < k → pt = T).

Section model.

(** [cfg] is the (fixed) set of voters; [id] the node being described. *)
Context (cfg : gset w64) (id : w64).

Definition is_quorum (q : gset w64) : Prop := size cfg < 2 * size (q ∩ cfg).

(** Two quorums meet.  This is the whole content of election safety; the same
    lemma, for the same [is_quorum], is proved in [readonly.v]. *)
Lemma quorums_intersect (q1 q2 : gset w64) :
  is_quorum q1 → is_quorum q2 → ∃ x, x ∈ q1 ∧ x ∈ q2.
Proof.
  intros Hsize1 Hsize2.
  destruct (decide (q1 ∩ q2 = ∅)) as [Hempty|Hne].
  2:{ apply set_choose_L in Hne as [x Hx]. exists x. set_solver. }
  exfalso.
  have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg by set_solver.
  have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) by set_solver.
  apply subseteq_size in Hunion.
  rewrite size_union in Hunion; [|done].
  unfold is_quorum in *.
  lia.
Qed.

Definition granted (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = true) votes).
Definition rejected (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = false) votes).

(** Putting messages on the network. *)
Definition psend_msgs (s : pstate.t) (ms : list msg.t) : pstate.t :=
  s <| pstate.outbox := s.(pstate.outbox) ++ ms |>.

Lemma psend_msgs_outbox s ms : (psend_msgs s ms).(pstate.outbox) = s.(pstate.outbox) ++ ms.
Proof. done. Qed.
Lemma psend_msgs_term s ms : (psend_msgs s ms).(pstate.term) = s.(pstate.term).
Proof. done. Qed.
Lemma psend_msgs_role s ms : (psend_msgs s ms).(pstate.role) = s.(pstate.role).
Proof. done. Qed.
Lemma psend_msgs_votes s ms : (psend_msgs s ms).(pstate.votes) = s.(pstate.votes).
Proof. done. Qed.
Lemma psend_msgs_log s ms : (psend_msgs s ms).(pstate.log) = s.(pstate.log).
Proof. done. Qed.
Lemma psend_msgs_commit s ms : (psend_msgs s ms).(pstate.commit) = s.(pstate.commit).
Proof. done. Qed.
Lemma psend_msgs_matched s ms : (psend_msgs s ms).(pstate.matched) = s.(pstate.matched).
Proof. done. Qed.
Lemma psend_msgs_base s ms : (psend_msgs s ms).(pstate.base) = s.(pstate.base).
Proof. done. Qed.

(** [lastIndex()] of the log, as a [w64]. *)
Definition plast_index (s : pstate.t) : w64 :=
  W64 (plog_last_index_Z s.(pstate.base) s.(pstate.log)).

(** ** Role transitions

    These mirror the Go code exactly.  [reset(term)] clears [Vote] only when
    the term actually changes, always clears [lead] and the vote tally; the
    [becomeX] wrappers then set [lead] and [state].  None of them sends, so
    all three carry the outbox across unchanged, and none touches the log.
    A non-leader's [matched] is [∅] (see [pstate.t]); a new leader's is
    whatever [reset] left, which [step_win] pins with [leader_match_ok]. *)

Definition pbecome_follower (s : pstate.t) (term lead : w64) : pstate.t :=
  {| pstate.term := term;
     pstate.vote := if decide (term = s.(pstate.term))
                    then s.(pstate.vote) else W64 0;
     pstate.lead := lead;
     pstate.role := role.Follower;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox);
     pstate.base := s.(pstate.base);
     pstate.log := s.(pstate.log);
     pstate.commit := s.(pstate.commit);
     pstate.matched := ∅ |}.

Definition pbecome_candidate (s : pstate.t) : pstate.t :=
  {| pstate.term := word.add s.(pstate.term) (W64 1);
     pstate.vote := id;
     pstate.lead := W64 0;
     pstate.role := role.Candidate;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox);
     pstate.base := s.(pstate.base);
     pstate.log := s.(pstate.log);
     pstate.commit := s.(pstate.commit);
     pstate.matched := ∅ |}.

Definition pbecome_leader (s : pstate.t) (mt : gmap w64 w64) : pstate.t :=
  {| pstate.term := s.(pstate.term);
     pstate.vote := s.(pstate.vote);
     pstate.lead := id;
     pstate.role := role.Leader;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox);
     pstate.base := s.(pstate.base);
     pstate.log := s.(pstate.log);
     pstate.commit := s.(pstate.commit);
     pstate.matched := mt |}.

(** What [reset] leaves in [Progress.Match] ([raft.go:779-808]): [0] for
    every voter, then [lastIndex()] for the node itself.  Stated without
    the voter set: a [0] claims nothing. *)
Definition leader_match_ok (s : pstate.t) (mt : gmap w64 w64) : Prop :=
  mt !! id = Some (plast_index s) ∧
  ∀ v x, v ≠ id → mt !! v = Some x → x = W64 0.

(** The empty entry a new leader appends ([pb.Entry{Data: nil}], the zero
    [Entry]), stamped at the leader's term and the log's next index; the
    protocol reading of [leader_entry] ([defs.v]). *)
Definition pleader_entry (s : pstate.t) : raftpb.Entry.t :=
  stamp s.(pstate.term) (plast_index s) 0 (zero_val raftpb.Entry.t).

Definition pappend (s : pstate.t) (es : list raftpb.Entry.t) : pstate.t :=
  s <| pstate.log := s.(pstate.log) ++ es |>.

(** A candidate that has just won: [becomeLeader] up to its [send]. *)
Definition pwin_state (s : pstate.t) (mt : gmap w64 w64) : pstate.t :=
  pappend (pbecome_leader s mt) [pleader_entry s].

(** [appendEntry]'s self-acknowledgement: a [MsgAppResp] to itself at the
    new last index, which [Step(MsgAppResp)] later turns into the leader's
    own [Match]. *)
Definition pself_ack (s : pstate.t) : msg.t :=
  msg.mk mtype.AppResp id id s.(pstate.term) false (plast_index s)
    (W64 0) (W64 0) (W64 0) [].

(** [campaign]'s vote request to [to], carrying the last entry id it read
    ([Index: last.index, LogTerm: last.term]). *)
Definition pvote_req (to term : w64) (last : raft.entryID.t) : msg.t :=
  msg.mk mtype.Vote id to term false
    last.(raft.entryID.index') last.(raft.entryID.term') (W64 0) (W64 0) [].

(** Receiving a message from the leader of the current term:
    [stepFollower]'s [r.lead = m.From] or [stepCandidate]'s
    [becomeFollower(m.Term, m.From)], which agree on [pstate] (a follower's
    [votes] are [∅]; the vote is kept at the same term). *)
Definition padopt_leader (s : pstate.t) (from : w64) : pstate.t :=
  s <| pstate.lead := from |> <| pstate.role := role.Follower |>
    <| pstate.votes := ∅ |> <| pstate.matched := ∅ |>.

Definition match_of (s : pstate.t) (v : w64) : w64 :=
  default (W64 0) (s.(pstate.matched) !! v).

(** The voters whose [Match] is at least [n]. *)
Definition acked_by (s : pstate.t) (n : w64) : gset w64 :=
  dom (filter (λ '(_, x), uint.Z n ≤ uint.Z x) s.(pstate.matched)).

(** [raft.trk.RecordVote]: the first vote recorded for a node wins; later
    ones are dropped. *)
Definition record_vote (votes : gmap w64 bool) (from : w64) (v : bool)
  : gmap w64 bool :=
  match votes !! from with Some _ => votes | None => <[from := v]> votes end.

(** A node may grant its vote to [from] in its current term when it has not
    already voted for somebody else and does not currently recognise a
    leader. *)
Definition pcan_vote (s : pstate.t) (from : w64) : Prop :=
  s.(pstate.vote) = from ∨ (s.(pstate.vote) = W64 0 ∧ s.(pstate.lead) = W64 0).

(** A node that is not leader never records itself as the leader.  An
    invariant of every reachable state ([own_raft_ghost] carries it): the
    rules that adopt a sender as leader ([step_higher_term] for a
    [from_leader] message, [step_app_*], [step_heartbeat]) require the
    sender to be another node, [step_campaign]/[step_lose] clear [lead],
    and [pbecome_leader] sets it only together with [role.Leader].  [Step]
    needs it for a forwarded proposal: [send] [Panicf]s on a message to
    oneself ([stepFollower]'s [MsgProp] premise [lead ≠ id]). *)
Definition lead_ok (s : pstate.t) : Prop :=
  s.(pstate.role) ≠ role.Leader → s.(pstate.lead) ≠ id.

(** A follower's vote tally is empty.  Also an invariant ([own_raft_ghost]
    carries it): every rule that makes a follower clears the tally
    ([pbecome_follower], [padopt_leader]), and [step_record_vote] needs a
    candidate.  [Step] needs it where the code and the model take
    different routes to the same follower: a follower at the current term
    receiving [MsgApp]/[MsgHeartbeat] runs [r.lead = m.From], leaving the
    tally alone, where [padopt_leader] sets it to [∅]. *)
Definition follower_votes_ok (s : pstate.t) : Prop :=
  s.(pstate.role) = role.Follower → s.(pstate.votes) = ∅.

(** What a leader's [MsgApp] says ([maybeSendAppend]: [Index: pr.Next-1,
    LogTerm: term(pr.Next-1), Entries: entries(pr.Next, maxMsgSize),
    Commit: committed]).

    [(index, logterm)] is an entry of the leader's log ([raftLog.term]
    pins the term it returns), and the entries are the leader's from
    [index + 1] on, cut short ([raftLog.entries] / [raftLog.slice] return a
    prefix of the log from the index asked for).  [app_payload_ok] is what
    a receiver needs of the batch itself ([raftLog.maybeAppend]'s premises);
    the sender has it from its own log's well-formedness, no-wrap and
    no-conf-change facts ([app_payload_from_log]), and [is_message] carries
    it. *)
Definition app_ok (s : pstate.t) (m : msg.t) : Prop :=
  m.(msg.ty) = mtype.App ∧ m.(msg.from) = id ∧ m.(msg.term) = s.(pstate.term) ∧
  m.(msg.to) ≠ id ∧
  plog_term_at s.(pstate.base) s.(pstate.log) m.(msg.index) = Some m.(msg.logterm) ∧
  uint.Z m.(msg.commit) ≤ uint.Z s.(pstate.commit) ∧
  Forall (λ e, e ∈ s.(pstate.log)) m.(msg.entries) ∧
  m.(msg.entries) `prefix_of` plog_from s.(pstate.base) s.(pstate.log)
                                (word.add m.(msg.index) (W64 1)) ∧
  app_payload_ok m.

(** [maybeSendSnapshot]'s [MsgSnap]: from the leader of the current term,
    carrying the metadata [(logterm, index)] of the snapshot
    [raftLog.snapshot] returned ([abs_snap], [defs.v]): non-empty, **at or
    below the commit index, and an entry id of the leader's log** -- the
    log has [logterm] at [index], possibly as its base.

    The last two are conjuncts since 2026-10-03.  They are what a receiver
    needs ([is_message]'s [Snap] case: [is_committed index] and the
    leader-prefix fact at [(logterm, index)]), and [snap_ok_message] builds
    that from them.  The sender has them from [raftLog.snapshot]'s spec: a
    pending snapshot is the log's own base; a [Storage] snapshot is the
    storage's current one, which [own_raftLog] keeps at or below
    [committed] and in the log ([stored_snap_ok], [inv_raftlog.v]).  The
    voters are not constrained here (the receiver's [Step] takes them as a
    transport premise). *)
Definition snap_ok (s : pstate.t) (m : msg.t) : Prop :=
  m.(msg.ty) = mtype.Snap ∧ m.(msg.from) = id ∧ m.(msg.term) = s.(pstate.term) ∧
  m.(msg.to) ≠ id ∧ m.(msg.index) ≠ W64 0 ∧
  uint.Z m.(msg.index) ≤ uint.Z s.(pstate.commit) ∧
  plog_term_at s.(pstate.base) s.(pstate.log) m.(msg.index) = Some m.(msg.logterm).

(** What [maybeSendAppend] may send: an [App], or (when the log no longer
    has what the peer needs) a [Snap]. *)
Definition repl_ok (s : pstate.t) (m : msg.t) : Prop := app_ok s m ∨ snap_ok s m.

(** [sendHeartbeat]: [Commit: min(pr.Match, committed)]. *)
Definition heartbeat_ok (s : pstate.t) (m : msg.t) : Prop :=
  m.(msg.ty) = mtype.Heartbeat ∧ m.(msg.from) = id ∧ m.(msg.term) = s.(pstate.term) ∧
  m.(msg.to) ≠ id ∧
  uint.Z m.(msg.commit) ≤ uint.Z s.(pstate.commit) ∧
  uint.Z m.(msg.commit) ≤ uint.Z (match_of s m.(msg.to)).

(** ** The transition relation

    [step s recv s'] says: a node in state [s], making use of the
    already-sent messages [recv], may move to state [s'].  Messages the node
    itself sends are not a separate output: they are the growth of
    [s'.(pstate.outbox)].

    Reflexivity and transitivity are part of the relation so that a single
    Go function which performs several protocol steps refines a single
    [step]. *)

Inductive step : pstate.t → list msg.t → pstate.t → Prop :=
(** Structural rules. *)
| step_refl s :
  step s [] s
| step_trans s₀ r₁ s₁ r₂ s₂ :
  step s₀ r₁ s₁ →
  step s₁ r₂ s₂ →
  step s₀ (r₁ ++ r₂) s₂

(** [Step]'s term preamble: a message from a higher term makes the node step
    down.  It adopts the sender as leader exactly when the message is one
    only a leader sends. *)
| step_higher_term m s :
  uint.Z s.(pstate.term) < uint.Z m.(msg.term) →
  m.(msg.to) = id →
  (** a leader's message is from another node ([send] never queues a
      leader message to oneself), so adopting its sender keeps [lead_ok] *)
  (from_leader m.(msg.ty) = true → m.(msg.from) ≠ id) →
  step s [m]
       (pbecome_follower s m.(msg.term)
          (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))

(** [hup] / [campaign]: a non-leader starts an election.  It increments its
    term, votes for itself, and sends a [MsgVote] to every other voter plus a
    self-addressed [MsgVoteResp] (which the Go code routes through
    [msgsAfterAppend]).  Each request carries the candidate's last entry
    id ([Index: last.index, LogTerm: last.term]): [campaign] reads
    [lastEntryID()] once per peer, and nothing in between changes the log. *)
| step_campaign s peers :
  s.(pstate.role) ≠ role.Leader →
  id ∈ cfg →
  (** The term increments, and a term that wrapped round to one the node has
      already voted in would let it vote twice in that term. *)
  uint.Z s.(pstate.term) + 1 < 2 ^ 64 →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  let s' := pbecome_candidate s in
  step s []
       (psend_msgs s'
          ([msg.plain mtype.VoteResp id id s'.(pstate.term) false] ++
           ((λ to, pvote_req to s'.(pstate.term)
                     (plog_last s.(pstate.base) s.(pstate.log))) <$> peers)))

(** Granting a vote: the candidate's last entry, as the request reports
    it, is at least as recent as ours ([raftLog.isUpToDate]).  Leader
    completeness rests on this check. *)
| step_grant_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  (** [W64 0] is the Go code's [None], so a vote *for* it is not a vote at
      all. *)
  m.(msg.from) ≠ W64 0 →
  m.(msg.term) = s.(pstate.term) →
  pcan_vote s m.(msg.from) →
  plog_up_to_date s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) = true →
  step s [m]
       (psend_msgs (s <| pstate.vote := m.(msg.from) |>)
          [msg.plain mtype.VoteResp id m.(msg.from) s.(pstate.term) false])

(** Refusing a vote.  Always legal. *)
| step_reject_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  step s [m]
       (psend_msgs s
          [msg.plain mtype.VoteResp id m.(msg.from) s.(pstate.term) true])

(** [stepCandidate] / [poll]: record a vote response for the current term. *)
| step_record_vote m s :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Candidate →
  step s [m]
       (s <| pstate.votes :=
              record_vote s.(pstate.votes) m.(msg.from) (negb m.(msg.reject)) |>)

(** Winning: a quorum of grants makes the candidate leader ([becomeLeader]:
    [reset], whose [Match] values [leader_match_ok] pins, then [appendEntry]
    of the empty entry, which queues the self-acknowledgement), and it
    immediately broadcasts ([bcastAppend]).

    The broadcast is deliberately loose: **any** list of messages
    [maybeSendAppend] may send, including none at all; see
    [spec_raft__bcastAppend.v] for why one per peer would be false. *)
| step_win s mt ms :
  s.(pstate.role) = role.Candidate →
  is_quorum (granted s.(pstate.votes)) →
  (** the leader's entry, at [lastIndex() + 1], does not wrap: the code's
      [own_raftLog] [Hnowrap] of the candidate's log (2026-10-03; without
      it a wrapped entry, at index [0], makes [isUpToDate] wrong and Leader
      Completeness false at [2^64] entries) *)
  plog_last_index_Z s.(pstate.base) s.(pstate.log) + 1 < 2 ^ 64 →
  leader_match_ok s mt →
  Forall (repl_ok (pwin_state s mt)) ms →
  step s [] (psend_msgs (pwin_state s mt) ([pself_ack (pwin_state s mt)] ++ ms))

(** Losing: [VoteLost] is "the voters who have not rejected are not a
    quorum" (see the 2026-09 history in notes/false-statements.md). *)
| step_lose s :
  s.(pstate.role) = role.Candidate →
  ¬ is_quorum (cfg ∖ rejected s.(pstate.votes)) →
  step s [] (pbecome_follower s s.(pstate.term) (W64 0))

(** [Ready] hands the pending messages to the transport, emptying the queues.
    Dropping messages from one's own outbox is always legal. *)
| step_drain s o' :
  o' ⊆+ s.(pstate.outbox) →
  step s [] (s <| pstate.outbox := o' |>)

(** *** Log replication (phase 1 of notes/raft-replication-model.md)

    Every rule below is about a message of the node's current term: a
    higher-term message has already been through [step_higher_term]. *)

(** [handleAppendEntries], accepting: [maybeAppend] matched [(logterm,
    index)].  The log becomes [plog_maybe_append]'s, [committed] moves to
    [min(m.Commit, lastnewi)] (never back), and the node acknowledges
    [lastnewi].  The conflict premise is what makes [maybeAppend]'s
    [Panicf] dead; [app_no_conflict_below_commit] is the protocol fact. *)
| step_app_accept m s lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) ≤ uint.Z m.(msg.index) →
  plog_maybe_append s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  (let ci := plog_find_conflict s.(pstate.base) s.(pstate.log) m.(msg.entries) in
   ci = W64 0 ∨ uint.Z s.(pstate.commit) < uint.Z ci) →
  let s1 := padopt_leader s m.(msg.from) in
  step s [m]
       (psend_msgs
          (s1 <| pstate.log := es' |>
              <| pstate.commit := plog_commit_to s.(pstate.commit)
                                    (if decide (uint.Z m.(msg.commit) < uint.Z lastnewi)
                                     then m.(msg.commit) else lastnewi) |>)
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false lastnewi
             (W64 0) (W64 0) (W64 0) []])

(** [handleAppendEntries], [a.prev.index < committed]: acknowledge the
    commit index. *)
| step_app_stale m s :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z m.(msg.index) < uint.Z s.(pstate.commit) →
  step s [m]
       (psend_msgs (padopt_leader s m.(msg.from))
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false s.(pstate.commit)
             (W64 0) (W64 0) (W64 0) []])

(** [handleAppendEntries], rejecting: the log does not have [(logterm,
    index)].  The hint is an optimisation; any is allowed. *)
| step_app_reject m s (hint hintterm : w64) :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) ≤ uint.Z m.(msg.index) →
  ¬ plog_matches s.(pstate.base) s.(pstate.log)
      (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
  step s [m]
       (psend_msgs (padopt_leader s m.(msg.from))
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) true m.(msg.index)
             hintterm (W64 0) hint []])

(** [handleHeartbeat]: [commitTo(m.Commit)], whose [Panicf] the premise
    rules out ([heartbeat_commit_le_last]). *)
| step_heartbeat m s :
  m.(msg.ty) = mtype.Heartbeat →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z m.(msg.commit) ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) →
  step s [m]
       (psend_msgs
          (padopt_leader s m.(msg.from)
             <| pstate.commit := plog_commit_to s.(pstate.commit) m.(msg.commit) |>)
          [msg.plain mtype.HeartbeatResp id m.(msg.from) s.(pstate.term) false])

(** [MsgBeat] / [bcastHeartbeat]: any heartbeats [heartbeat_ok] allows. *)
| step_beat s ms :
  s.(pstate.role) = role.Leader →
  Forall (heartbeat_ok s) ms →
  step s [] (psend_msgs s ms)

(** [stepLeader]'s [MsgAppResp], accepting: [pr.MaybeUpdate(m.Index)]
    raises the sender's [Match].  A *rejecting* [AppResp] changes no
    protocol state ([MaybeDecrTo] moves [Next], not [Match]): [step_refl]. *)
| step_app_resp m s (x : w64) :
  m.(msg.ty) = mtype.AppResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Leader →
  m.(msg.reject) = false →
  s.(pstate.matched) !! m.(msg.from) = Some x →
  step s [m]
       (s <| pstate.matched :=
              <[m.(msg.from) := if decide (uint.Z x < uint.Z m.(msg.index))
                                then m.(msg.index) else x]> s.(pstate.matched) |>)

(** [maybeCommit]: a quorum's [Match] reaches [n], and the entry there is of
    the leader's own term. *)
| step_commit s (n : w64) :
  s.(pstate.role) = role.Leader →
  uint.Z s.(pstate.commit) < uint.Z n →
  uint.Z n ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) →
  plog_term_at s.(pstate.base) s.(pstate.log) n = Some s.(pstate.term) →
  is_quorum (acked_by s n) →
  step s [] (s <| pstate.commit := n |>)

(** [bcastAppend] / [sendAppend] outside an election win. *)
| step_send_apps s ms :
  s.(pstate.role) = role.Leader →
  Forall (repl_ok s) ms →
  step s [] (psend_msgs s ms)

(** [MsgProp] at the leader: [appendEntry] of the batch, which queues the
    self-acknowledgement.  [EntryNormal] only: no conf change in phase 1. *)
| step_propose s ents :
  s.(pstate.role) = role.Leader →
  Forall (λ e, e.(raftpb.Entry.Type') = W32 0) ents →
  (** the stamped indices do not wrap ([appendEntry]'s [Hsmall] and the
      log's own bound give it) *)
  plog_last_index_Z s.(pstate.base) s.(pstate.log) + Z.of_nat (length ents) < 2 ^ 64 →
  let s' := pappend s (imap (stamp s.(pstate.term) (plast_index s)) ents) in
  step s [] (psend_msgs s' [pself_ack s'])

(** [MsgProp] at a follower that knows a leader: forwarded, with [Term]
    left at [0] ([send]'s [MsgProp] exception) and [From] stamped. *)
| step_prop_forward m s :
  m.(msg.ty) = mtype.Propose →
  s.(pstate.role) = role.Follower →
  s.(pstate.lead) ≠ W64 0 →
  step s [m]
       (psend_msgs s
          [msg.mk mtype.Propose id s.(pstate.lead) (W64 0) m.(msg.reject)
             m.(msg.index) m.(msg.logterm) m.(msg.commit) m.(msg.rejecthint)
             m.(msg.entries)])

(** *** Snapshots (phase 2 of notes/raft-replication-model.md)

    [handleSnapshot] (raft.go:1827) after [stepFollower]'s [r.lead =
    m.From] / [stepCandidate]'s [becomeFollower(m.Term, m.From)] -- the
    leader is adopted, as for an [App] ([padopt_leader]).  [restore(s)]
    (raft.go:1849) returns [false] when [Metadata.Index ≤ committed]
    ([step_snap_stale]); when the node is not a follower (dead: both callers
    have just made it one); when [r.id] is in none of the [ConfState]'s sets
    (dead under the fixed voter set: the voters are [cfg] and [id ∈ cfg],
    premises below); and when the log already has [(Term, Index)], after
    [commitTo(Index)] ([step_snap_fastfwd]).  Otherwise the log is replaced
    by the snapshot ([step_snap_restore]).  The reply is [MsgAppResp{Index:
    lastIndex()}] after a restore -- [Index], the unstable log being empty
    at offset [Index + 1] -- and [MsgAppResp{Index: committed}] otherwise:
    [Index] after the fast-forward, the old commit index when stale.  The
    voter premise is on the message's [voters]: under the fixed-voter-set
    scope [Step] takes it as a transport premise. *)

(** [restore] proper: [raftLog.restore] makes the snapshot the compaction
    boundary, with nothing after it, and commits it. *)
| step_snap_restore m s :
  m.(msg.ty) = mtype.Snap →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  m.(msg.voters) ≡ₚ elements cfg →
  id ∈ cfg →
  uint.Z s.(pstate.commit) < uint.Z m.(msg.index) →
  ¬ plog_matches s.(pstate.base) s.(pstate.log)
      (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
  step s [m]
       (psend_msgs
          (padopt_leader s m.(msg.from)
             <| pstate.base := raft.entryID.mk m.(msg.logterm) m.(msg.index) |>
             <| pstate.log := [] |>
             <| pstate.commit := m.(msg.index) |>)
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false m.(msg.index)
             (W64 0) (W64 0) (W64 0) []])

(** The log already has the snapshot's last entry: [commitTo(Index)] only. *)
| step_snap_fastfwd m s :
  m.(msg.ty) = mtype.Snap →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  m.(msg.voters) ≡ₚ elements cfg →
  id ∈ cfg →
  uint.Z s.(pstate.commit) < uint.Z m.(msg.index) →
  plog_matches s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
  step s [m]
       (psend_msgs
          (padopt_leader s m.(msg.from) <| pstate.commit := m.(msg.index) |>)
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false m.(msg.index)
             (W64 0) (W64 0) (W64 0) []])

(** An obsolete snapshot: acknowledge the commit index. *)
| step_snap_stale m s :
  m.(msg.ty) = mtype.Snap →
  m.(msg.to) = id →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z m.(msg.index) ≤ uint.Z s.(pstate.commit) →
  step s [m]
       (psend_msgs (padopt_leader s m.(msg.from))
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false s.(pstate.commit)
             (W64 0) (W64 0) (W64 0) []])
.

End model.

(** ** Ghost state

    The ghost state is deliberately *node-local*: there is no Iris invariant
    here and nothing global to open.  Each node owns the authority over its
    own histories, and that authority is the exclusive part of
    [own_raft_ghost].  Everything a step needs to *learn* is persistent
    knowledge, so it can ride on a message or be held across a step with
    nowhere to put it.

    Election:

    - [is_vote γ v term cand] — node [v] voted for [cand] in [term].  Frozen
      into [v]'s map when it is allocated, so it is persistent, and
      unforgeable because allocating it takes [v]'s own authority.
    - [is_leader γ id term] — a quorum of [is_vote]s for [id] at [term].

    Election safety is quorum intersection plus the agreement of two
    [is_vote]s for one node and term; that is all [is_leader_unique] is.
    What holds a node to one vote per term is [vote_hist_ok].

    Replication (2026-10-01):

    - [is_term_log γ v t γt] — node [v], as leader of term [t], keeps the
      entries it created in [t] in the ghost map [γt] ([index ↦ entry]).
      Frozen into [v]'s per-node map [re_terms] when [v] becomes leader in
      [t] ([step_win]); a node is leader in a term at most once, and
      [terms_ok] is what says so.
    - [is_entry γ e] — the leader of [e]'s term created [e] at [e]'s index.
      Two [is_entry]s at one [(term, index)] agree ([is_entry_agree]): the
      leaders agree by [is_leader_unique], their term logs by the frozen
      map, the entries by the term log's.
    - [is_acked γ v t i] — [v] acknowledged the leader of [t] up to [i]
      (frozen into [v]'s map [re_acks]); [i = 0] is free.
    - [is_committed γ i] — a quorum acknowledged some term's leader up to
      at least [i]; [i = 0] is free.

    [is_message] attaches these to the messages that report them, and
    [own_raft_ghost] keeps the leader's [is_acked] for every [Match] and
    [is_committed] of its commit index.

    Replication safety (2026-10-02):

    - The term log of [(v, t)] also records [v]'s base and log when it won
      [t] ([is_term_log γ v t γt b l0]), and holds each entry [v] creates
      in [t] with its predecessor's term: [is_entry_r γ e pt].
    - [log_recs γ b es]: every entry of a log has [is_entry_r] with its
      predecessor's term *in that log*.  [own_log_ghost] keeps it of the
      node's log, with [log_ok] (well-formed in range, [base ≤ commit ≤
      lastIndex()]).  Log Matching follows from two logs' records alone.
    - [lead_prefix γ ldr t bL l]: [l] is a log the leader of [t] had.  An
      [App] or [Snap] carries one, covering what it says.
    - [ack_agree]: a log agrees at [i] with a [lead_prefix] of [t].
      [own_log_ghost] keeps it ([acks_ok]) of every acknowledgement a
      non-leader made in its current term above its commit index, and
      that a node acknowledges only at its own term ([acks_term]).  A
      [Heartbeat] carries the acknowledgement its [Commit] is bounded by.
      That is [heartbeat_commit_le_last]. *)

Record raft_election_names := {
    (** The voter set this ghost state is about.  It lives in [γ] rather than
        being a parameter of [own_raft_ghost_step]: a step free to choose its
        own [cfg] could choose a singleton one and elect itself. *)
    re_cfg : gset w64;
    (** [re_votes !! id] names the ghost map holding node [id]'s vote
        history, [term ↦ candidate].  A node absent from here has no ghost
        state at all. *)
    re_votes : gmap w64 gname;
    (** [re_terms !! id]: node [id]'s map [term ↦ (γt, base, log)] of the
        term logs it allocated as leader ([is_term_log]). *)
    re_terms : gmap w64 gname;
    (** [re_acks !! id]: node [id]'s acknowledgements, [(term, index) ↦ ()]. *)
    re_acks : gmap w64 gname;
    (** [re_camp !! id]: node [id]'s campaign records, [term ↦ full log]
        when it started the election of that term ([is_camp], 2026-10-03). *)
    re_camp : gmap w64 gname;
    (** [re_vlogs !! id]: node [id]'s vote-time logs, [k ↦ (term, full
        log)], one per vote it cast ([is_vlog], 2026-10-03). *)
    re_vlogs : gmap w64 gname;
  }.

Section ghost.
Context `{!invGS Σ, !allG Σ}.

Implicit Type γ : raft_election_names.

(** *** Votes *)

Definition is_vote γ (v term cand : w64) : iProp Σ :=
  ∃ γv, ⌜ γ.(re_votes) !! v = Some γv ⌝ ∗ term ↪[γv]□ cand.

Global Instance is_vote_pers γ v term cand : Persistent (is_vote γ v term cand).
Proof. apply _. Qed.
Global Instance is_vote_timeless γ v term cand : Timeless (is_vote γ v term cand).
Proof. apply _. Qed.

(** One vote per node per term.  This is the other half of election safety. *)
Lemma is_vote_agree γ v term c1 c2 :
  is_vote γ v term c1 -∗ is_vote γ v term c2 -∗ ⌜ c1 = c2 ⌝.
Proof.
  iIntros "(%γ1 & %Hγ1 & H1) (%γ2 & %Hγ2 & H2)".
  rewrite Hγ1 in Hγ2. injection Hγ2 as <-.
  iApply (ghost_map_elem_agree with "H1 H2").
Qed.

(** *** Leadership *)

Definition is_leader γ (id term : w64) : iProp Σ :=
  ∃ q, ⌜ is_quorum γ.(re_cfg) q ⌝ ∗ [∗ set] v ∈ q, is_vote γ v term id.

Global Instance is_leader_pers γ id term : Persistent (is_leader γ id term).
Proof. apply _. Qed.
Global Instance is_leader_timeless γ id term : Timeless (is_leader γ id term).
Proof. apply _. Qed.

(** ** Election safety

    Two leaders in one term were each elected by a quorum; the quorums meet
    in a voter that cast one vote. *)
Lemma is_leader_unique γ id1 id2 term :
  is_leader γ id1 term -∗ is_leader γ id2 term -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros "(%q1 & %Hq1 & #H1) (%q2 & %Hq2 & #H2)".
  destruct (quorums_intersect _ _ _ Hq1 Hq2) as (v & Hv1 & Hv2).
  iDestruct (big_sepS_elem_of _ _ _ Hv1 with "H1") as "Hv1".
  iDestruct (big_sepS_elem_of _ _ _ Hv2 with "H2") as "Hv2".
  iApply (is_vote_agree with "Hv1 Hv2").
Qed.

(** *** Entries, acknowledgements, commitment *)

(** [v]'s term log of term [t]: the ghost map [γt], and [v]'s compaction
    boundary [b] and log [l0] (the entries after [b]) at the moment it won
    [t].  Neither changes while [v] leads [t] (a leader never restores a
    snapshot and never truncates), so every log [v] has in [t] is [l0]
    followed by entries [v] created in [t], and [γt] holds those, each with
    its predecessor's term. *)
Definition is_term_log γ (v t : w64) (γt : gname) (b : raft.entryID.t)
    (l0 : list raftpb.Entry.t) : iProp Σ :=
  ∃ γm, ⌜ γ.(re_terms) !! v = Some γm ⌝ ∗ t ↪[γm]□ (γt, b, l0).

(** [c]'s campaign record of term [T]: its full log ([fp ++ log], see
    "Full logs") when it became candidate in [T] -- unchanged until it wins
    ([camp_own]), so it is also the log the leader of [T] started from.
    Frozen when allocated ([step_campaign]); a [Vote] request carries it
    ([is_message]), so the [(LogTerm, Index)] a voter checks is the last
    entry of a log the candidate really had.  Every term in it is below [T]
    (the candidate has nothing of its own term), which is [camp_ok].
    (2026-10-03.) *)
Definition is_camp γ (c T : w64) (F : list raftpb.Entry.t) : iProp Σ :=
  ∃ γc, ⌜ γ.(re_camp) !! c = Some γc ∧ camp_ok T F ⌝ ∗ T ↪[γc]□ F.

Global Instance is_camp_pers γ c T F : Persistent (is_camp γ c T F).
Proof. apply _. Qed.
Global Instance is_camp_timeless γ c T F : Timeless (is_camp γ c T F).
Proof. apply _. Qed.

Lemma is_camp_agree γ c T F1 F2 :
  is_camp γ c T F1 -∗ is_camp γ c T F2 -∗ ⌜ F1 = F2 ⌝.
Proof.
  iIntros "(%γ1 & [%H1 _] & Hf1) (%γ2 & [%H2 _] & Hf2)".
  rewrite H1 in H2. injection H2 as <-.
  iApply (ghost_map_elem_agree with "Hf1 Hf2").
Qed.

Lemma is_camp_ok γ c T F : is_camp γ c T F -∗ ⌜ camp_ok T F ⌝.
Proof. iIntros "(% & [_ %H] & _)". done. Qed.

(** [e] was created by the leader of its term, after an entry of term
    [pt]: the term log of [e]'s term holds [(e, pt)] at [e]'s index.  Since
    2026-10-03 also: [e] is past the leader's campaign log [F0], its
    predecessor is [F0]'s last entry or another entry of [e]'s term, and
    [pt ≤ e.term] ([pt_ok]) -- which makes the terms of a log with records
    non-decreasing, and lets Leader Completeness walk a log down from an
    entry of term [T] to where the leader of [T] started. *)
Definition is_entry_r γ (e : raftpb.Entry.t) (pt : w64) : iProp Σ :=
  ∃ ldr γt b l0 F0, is_leader γ ldr e.(raftpb.Entry.Term') ∗
                 is_term_log γ ldr e.(raftpb.Entry.Term') γt b l0 ∗
                 is_camp γ ldr e.(raftpb.Entry.Term') F0 ∗
                 e.(raftpb.Entry.Index') ↪[γt]□ (e, pt) ∗
                 ⌜ pt_ok F0 e.(raftpb.Entry.Term') (uint.Z e.(raftpb.Entry.Index')) pt ⌝.

Definition is_entry γ (e : raftpb.Entry.t) : iProp Σ := ∃ pt, is_entry_r γ e pt.

Definition is_acked γ (v t i : w64) : iProp Σ :=
  ⌜ uint.Z i = 0 ⌝ ∨
  ∃ γa, ⌜ γ.(re_acks) !! v = Some γa ⌝ ∗ (t, i) ↪[γa]□ ().

Global Instance is_term_log_pers γ v t γt b l0 : Persistent (is_term_log γ v t γt b l0).
Proof. apply _. Qed.
Global Instance is_term_log_timeless γ v t γt b l0 : Timeless (is_term_log γ v t γt b l0).
Proof. apply _. Qed.
Global Instance is_entry_r_pers γ e pt : Persistent (is_entry_r γ e pt).
Proof. apply _. Qed.
Global Instance is_entry_r_timeless γ e pt : Timeless (is_entry_r γ e pt).
Proof. apply _. Qed.
Global Instance is_entry_pers γ e : Persistent (is_entry γ e).
Proof. apply _. Qed.
Global Instance is_entry_timeless γ e : Timeless (is_entry γ e).
Proof. apply _. Qed.
Global Instance is_acked_pers γ v t i : Persistent (is_acked γ v t i).
Proof. apply _. Qed.
Global Instance is_acked_timeless γ v t i : Timeless (is_acked γ v t i).
Proof. apply _. Qed.

(** Log matching at one index: two entries with the same term and index
    are the same entry. *)
Lemma is_term_log_agree γ v t (γt1 : gname) b1 l1 (γt2 : gname) b2 l2 :
  is_term_log γ v t γt1 b1 l1 -∗ is_term_log γ v t γt2 b2 l2 -∗
  ⌜ γt1 = γt2 ∧ b1 = b2 ∧ l1 = l2 ⌝.
Proof.
  iIntros "(%γm1 & %Hγm1 & Ht1) (%γm2 & %Hγm2 & Ht2)".
  rewrite Hγm1 in Hγm2. injection Hγm2 as <-.
  iDestruct (ghost_map_elem_agree with "Ht1 Ht2") as %[= -> -> ->]. done.
Qed.

Lemma is_entry_r_agree γ e1 pt1 e2 pt2 :
  e1.(raftpb.Entry.Term') = e2.(raftpb.Entry.Term') →
  e1.(raftpb.Entry.Index') = e2.(raftpb.Entry.Index') →
  is_entry_r γ e1 pt1 -∗ is_entry_r γ e2 pt2 -∗ ⌜ e1 = e2 ∧ pt1 = pt2 ⌝.
Proof.
  iIntros (Ht Hi) "(%l1 & %γ1 & %b1 & %l01 & %F1 & #Hl1 & #Ht1 & _ & #He1 & _)
                   (%l2 & %γ2 & %b2 & %l02 & %F2 & #Hl2 & #Ht2 & _ & #He2 & _)".
  iEval (rewrite Ht) in "Hl1 Ht1". iEval (rewrite Hi) in "He1".
  iDestruct (is_leader_unique with "Hl1 Hl2") as %<-.
  iDestruct (is_term_log_agree with "Ht1 Ht2") as %(<- & _ & _).
  iDestruct (ghost_map_elem_agree with "He1 He2") as %[= -> ->]. done.
Qed.

Lemma is_entry_agree γ e1 e2 :
  e1.(raftpb.Entry.Term') = e2.(raftpb.Entry.Term') →
  e1.(raftpb.Entry.Index') = e2.(raftpb.Entry.Index') →
  is_entry γ e1 -∗ is_entry γ e2 -∗ ⌜ e1 = e2 ⌝.
Proof.
  iIntros (Ht Hi) "(%pt1 & #H1) (%pt2 & #H2)".
  iDestruct (is_entry_r_agree with "H1 H2") as %[? _]; done.
Qed.

(** A snapshot's metadata [(t, i)] names an entry some leader created: the
    last entry the snapshot covers.  Defined through [is_entry], not as new
    ghost state, so it agrees with every other [is_entry] at [(t, i)]
    ([is_entry_agree]): a snapshot's compacted prefix is no different from
    entries still in a log, it is only no longer stored.  (2026-10-02.) *)
Definition is_snap_meta γ (t i : w64) : iProp Σ :=
  ∃ e, is_entry γ e ∗
       ⌜ e.(raftpb.Entry.Term') = t ∧ e.(raftpb.Entry.Index') = i ⌝.

Global Instance is_snap_meta_pers γ t i : Persistent (is_snap_meta γ t i).
Proof. apply _. Qed.
Global Instance is_snap_meta_timeless γ t i : Timeless (is_snap_meta γ t i).
Proof. apply _. Qed.

(** A log's base [b] names a real entry, unless it is the initial [0]
    (2026-10-03).  [own_log_ghost] keeps it of the node's base: the only
    rule that moves the base, [step_snap_restore], moves it to a snapshot's
    metadata, which the message carries [is_snap_meta] for.  A leader
    whose [Storage] snapshot sits exactly at its base sends it with
    [is_snap_meta] from here ([snap_ok_message]); one above the base takes
    it from the log's records. *)
Definition base_ok γ (b : raft.entryID.t) : iProp Σ :=
  ⌜ uint.Z b.(raft.entryID.index') = 0 ⌝ ∨
  is_snap_meta γ b.(raft.entryID.term') b.(raft.entryID.index').

Global Instance base_ok_pers γ b : Persistent (base_ok γ b).
Proof. apply _. Qed.
Global Instance base_ok_timeless γ b : Timeless (base_ok γ b).
Proof. apply _. Qed.

(** *** Logs as persistent knowledge (2026-10-02)

    [log_recs γ b es]: every entry of the log (in range, [plog_wf_r]) is
    [is_entry_r] with its predecessor's term *in this log*.  Two logs that
    both have records agree wherever they share a term at an index, all the
    way down ([log_recs_agree], [plog_match_down]): that is Log Matching,
    and it needs nothing but the two logs' records -- the records agree
    because the term logs' fragments do.

    [lead_prefix γ ldr t bL l]: [l] (after [bL]) is a log the leader [ldr]
    of [t] had while leading [t].  It carries [l]'s records and, for every
    entry [ldr] created in [t], the term log's fragment -- so two
    [lead_prefix]es of one term agree wherever both have an entry
    ([lead_prefix_agree]): both are the term log's initial log [l0]
    followed by fragments of one ghost map. *)

Definition log_recs γ (b : raft.entryID.t) (es : list raftpb.Entry.t) : iProp Σ :=
  [∗ list] k ↦ e ∈ es,
    if decide (uint.Z b.(raft.entryID.index') + Z.of_nat k + 1 < 2 ^ 64)
    then ∃ pt, ⌜ plog_term_at b es (pidx b k) = Some pt ⌝ ∗ is_entry_r γ e pt
    else True.

Global Instance log_recs_pers γ b es : Persistent (log_recs γ b es).
Proof. rewrite /log_recs. apply big_sepL_persistent. intros. case_decide; apply _. Qed.
Global Instance log_recs_timeless γ b es : Timeless (log_recs γ b es).
Proof. rewrite /log_recs. apply big_sepL_timeless. intros. case_decide; apply _. Qed.

Definition lead_frags (γt : gname) (l0 l : list raftpb.Entry.t) : iProp Σ :=
  [∗ list] k ↦ e ∈ l,
    if decide (length l0 ≤ k)%nat then ∃ pt : w64, e.(raftpb.Entry.Index') ↪[γt]□ (e, pt)
    else True.

Global Instance lead_frags_pers γt l0 l : Persistent (lead_frags γt l0 l).
Proof. rewrite /lead_frags. apply big_sepL_persistent. intros. case_decide; apply _. Qed.
Global Instance lead_frags_timeless γt l0 l : Timeless (lead_frags γt l0 l).
Proof. rewrite /lead_frags. apply big_sepL_timeless. intros. case_decide; apply _. Qed.

Definition lead_prefix γ (ldr t : w64) (bL : raft.entryID.t) (l : list raftpb.Entry.t)
  : iProp Σ :=
  is_leader γ ldr t ∗
  ∃ γt l0, is_term_log γ ldr t γt bL l0 ∗ ⌜ plog_wf_r bL l ∧ l0 `prefix_of` l ⌝ ∗
           log_recs γ bL l ∗ lead_frags γt l0 l.

Global Instance lead_prefix_pers γ ldr t bL l : Persistent (lead_prefix γ ldr t bL l).
Proof. apply _. Qed.
Global Instance lead_prefix_timeless γ ldr t bL l : Timeless (lead_prefix γ ldr t bL l).
Proof. apply _. Qed.

Lemma log_recs_agree γ b1 es1 b2 es2 :
  log_recs γ b1 es1 -∗ log_recs γ b2 es2 -∗ ⌜ recs_agree b1 es1 b2 es2 ⌝.
Proof.
  iIntros "#H1 #H2".
  iAssert (∀ (k1 k2 : nat) e1 e2,
             ⌜ es1 !! k1 = Some e1 ∧ es2 !! k2 = Some e2 ∧
               uint.Z b1.(raft.entryID.index') + Z.of_nat k1 + 1 < 2 ^ 64 ∧
               uint.Z b2.(raft.entryID.index') + Z.of_nat k2 + 1 < 2 ^ 64 ∧
               e1.(raftpb.Entry.Term') = e2.(raftpb.Entry.Term') ∧
               e1.(raftpb.Entry.Index') = e2.(raftpb.Entry.Index') ⌝ -∗
             ⌜ e1 = e2 ∧ plog_term_at b1 es1 (pidx b1 k1)
                         = plog_term_at b2 es2 (pidx b2 k2) ⌝)%I as "#H".
  { iIntros (k1 k2 e1 e2 (Hk1 & Hk2 & Hr1 & Hr2 & Ht & Hi)).
    iDestruct (big_sepL_lookup with "H1") as "H1'"; first exact Hk1.
    iDestruct (big_sepL_lookup with "H2") as "H2'"; first exact Hk2.
    rewrite !decide_True //.
    iDestruct "H1'" as (pt1 Hpt1) "He1". iDestruct "H2'" as (pt2 Hpt2) "He2".
    iDestruct (is_entry_r_agree with "He1 He2") as %[-> ->]; [done|done|].
    iPureIntro. split; [done|]. by rewrite Hpt1 Hpt2. }
  iDestruct "H" as %H. iPureIntro.
  intros k1 k2 e1 e2 Hk1 Hk2 Hr1 Hr2 Ht Hi. by apply H.
Qed.

Lemma lead_prefix_base γ L1 L2 t b1 b2 l1 l2 :
  lead_prefix γ L1 t b1 l1 -∗ lead_prefix γ L2 t b2 l2 -∗ ⌜ b1 = b2 ⌝.
Proof.
  iIntros "(#Hl1 & %γ1 & %l01 & #Ht1 & _) (#Hl2 & %γ2 & %l02 & #Ht2 & _)".
  iDestruct (is_leader_unique with "Hl1 Hl2") as %<-.
  iDestruct (is_term_log_agree with "Ht1 Ht2") as %(_ & -> & _). done.
Qed.

Lemma lead_prefix_wf γ L t b l :
  lead_prefix γ L t b l -∗ ⌜ plog_wf_r b l ⌝ ∗ log_recs γ b l.
Proof. iIntros "(_ & % & % & _ & [%Hw _] & $ & _)". done. Qed.

(** Two logs of one term's leader agree wherever both have a term. *)
Lemma lead_prefix_agree γ L1 L2 t b l1 l2 (j : w64) :
  is_Some (plog_term_at b l1 j) → is_Some (plog_term_at b l2 j) →
  lead_prefix γ L1 t b l1 -∗ lead_prefix γ L2 t b l2 -∗
  ⌜ plog_term_at b l1 j = plog_term_at b l2 j ⌝.
Proof.
  iIntros ([t1 Ht1] [t2 Ht2])
    "(#Hl1 & %γ1 & %l01 & #Hlog1 & [%Hw1 %Hp1] & _ & #Hf1)
     (#Hl2 & %γ2 & %l02 & #Hlog2 & [%Hw2 %Hp2] & _ & #Hf2)".
  iDestruct (is_leader_unique with "Hl1 Hl2") as %<-.
  iDestruct (is_term_log_agree with "Hlog1 Hlog2") as %(<- & _ & <-).
  pose proof (plog_term_at_Some_range _ _ _ _ Ht1) as [Hb _].
  destruct (decide (uint.Z j = uint.Z b.(raft.entryID.index'))) as [Heq|Hne].
  { assert (j = b.(raft.entryID.index')) as -> by (apply word.unsigned_inj; lia).
    rewrite !plog_term_at_base //. }
  destruct (plog_term_at_Some_entry _ _ _ _ Hw1 Ht1 ltac:(lia)) as (x1 & Hx1 & Hi1 & Hxt1).
  destruct (plog_term_at_Some_entry _ _ _ _ Hw2 Ht2 ltac:(lia)) as (x2 & Hx2 & Hi2 & Hxt2).
  rewrite Ht1 Ht2 -Hxt1 -Hxt2.
  set (p := Z.to_nat (uint.Z j - uint.Z b.(raft.entryID.index') - 1)) in *.
  destruct (decide (p < length l01)%nat) as [Hlt|Hge].
  - destruct (lookup_lt_is_Some_2 l01 p Hlt) as [y Hy].
    pose proof (prefix_lookup_Some _ _ _ _ Hy Hp1) as Hy1.
    pose proof (prefix_lookup_Some _ _ _ _ Hy Hp2) as Hy2.
    rewrite Hx1 in Hy1. rewrite Hx2 in Hy2. by simplify_eq.
  - iDestruct (big_sepL_lookup with "Hf1") as "H1"; first exact Hx1.
    iDestruct (big_sepL_lookup with "Hf2") as "H2"; first exact Hx2.
    rewrite !decide_True; [|lia|lia].
    iDestruct "H1" as (pt1) "H1". iDestruct "H2" as (pt2) "H2".
    rewrite Hi1 Hi2.
    iDestruct (ghost_map_elem_agree with "H1 H2") as %[= -> _]. done.
Qed.

(** *** Full logs as persistent knowledge (2026-10-03)

    The records of a full log ([log_recs γ base0 F]) are those of its
    compacted prefix and of its stored suffix ([log_recs_full]).  From them:
    full logs match like stored ones ([full_match]), their terms never go
    down ([recs_mono]), and below an entry of term [T] they have [T] all the
    way to where [T]'s leader started ([recs_chain]). *)

Lemma log_recs_full γ b fp es :
  full_ok b fp → log_recs γ base0 fp -∗ log_recs γ b es -∗ log_recs γ base0 (fp ++ es).
Proof.
  iIntros (Hfull) "#H1 #H2". pose proof Hfull as (Hlen & _ & _).
  rewrite /log_recs big_sepL_app. iSplit.
  - iApply (big_sepL_impl with "H1"). iIntros "!> %k %x %Hk H".
    case_decide as Hr; [|done]. iDestruct "H" as (pt Hpt) "Hx". iExists pt. iFrame "Hx".
    iPureIntro. rewrite plog_term_at_app_l; [done|].
    apply lookup_lt_Some in Hk. rewrite /pidx base0_index word.unsigned_of_Z_nowrap.
    + rewrite /plog_last_index_Z base0_index. lia.
    + rewrite base0_index in Hr. lia.
  - iApply (big_sepL_impl with "H2"). iIntros "!> %k %x %Hk H".
    rewrite base0_index. iRevert "H".
    repeat case_decide; try lia; iIntros "H"; [|done].
    iDestruct "H" as (pt Hpt) "Hx". iExists pt. iFrame "Hx".
    iPureIntro.
    assert (Hp : pidx base0 (length fp + k) = pidx b k).
    { rewrite /pidx base0_index. f_equal. lia. }
    rewrite Hp (full_term_at b fp es) //.
    rewrite /pidx word.unsigned_of_Z_nowrap; [lia|].
    pose proof (word.unsigned_range b.(raft.entryID.index')). lia.
Qed.

Lemma log_recs_take γ F (n : nat) :
  log_recs γ base0 F -∗ log_recs γ base0 (take n F).
Proof.
  iIntros "#H". rewrite /log_recs.
  iApply big_sepL_intro. iIntros "!> %k %x %Hk".
  destruct (decide (k < n)%nat) as [Hlt|Hge];
    [|rewrite lookup_take_ge in Hk; [done|lia]].
  rewrite lookup_take_lt in Hk; [|done].
  iDestruct (big_sepL_lookup with "H") as "Hx"; first exact Hk.
  case_decide as Hr; [|done].
  iDestruct "Hx" as (pt Hpt) "Hx". iExists pt. iFrame "Hx". iPureIntro.
  rewrite plog_term_at_take_full; [done|].
  rewrite /pidx base0_index word.unsigned_of_Z_nowrap; [lia|].
  rewrite base0_index in Hr. lia.
Qed.

(** One entry's record, read out. *)
Lemma log_recs_lookup γ F (k : nat) e :
  F !! k = Some e → Z.of_nat k + 1 < 2 ^ 64 →
  log_recs γ base0 F -∗
  ∃ pt, ⌜ plog_term_at base0 F (W64 (Z.of_nat k)) = Some pt ⌝ ∗ is_entry_r γ e pt.
Proof.
  iIntros (Hk Hr) "#H".
  iDestruct (big_sepL_lookup with "H") as "Hx"; first exact Hk.
  rewrite base0_index decide_True; [|lia].
  iDestruct "Hx" as (pt Hpt) "Hx". iExists pt. iFrame "Hx". iPureIntro.
  rewrite /pidx base0_index Z.add_0_l in Hpt. done.
Qed.

Lemma is_entry_r_pt γ e pt :
  is_entry_r γ e pt -∗ ⌜ uint.Z pt ≤ uint.Z e.(raftpb.Entry.Term') ⌝.
Proof. iIntros "(% & % & % & % & % & _ & _ & _ & _ & %Hok)". iPureIntro. apply Hok. Qed.

(** Full-log matching: two full logs with records that have the same term
    at [i] agree everywhere below. *)
Lemma full_match γ F1 F2 (i : w64) :
  plog_wf base0 F1 → plog_wf base0 F2 →
  is_Some (plog_term_at base0 F1 i) →
  plog_term_at base0 F1 i = plog_term_at base0 F2 i →
  log_recs γ base0 F1 -∗ log_recs γ base0 F2 -∗
  ⌜ ∀ j : w64, uint.Z j ≤ uint.Z i →
      plog_term_at base0 F1 j = plog_term_at base0 F2 j ⌝.
Proof.
  iIntros (Hw1 Hw2 Hs Heq) "#H1 #H2".
  iDestruct (log_recs_agree with "H1 H2") as %HRA.
  iPureIntro. intros j Hj.
  apply (plog_match_down _ _ _ _ i (plog_wf_wf_r _ _ Hw1) (plog_wf_wf_r _ _ Hw2) HRA Hs Heq);
    rewrite ?base0_index; [word|word|lia].
Qed.

(** The compacted prefix of a log with records is determined by its base. *)
Lemma full_ok_unique γ b fp1 fp2 :
  full_ok b fp1 → full_ok b fp2 →
  log_recs γ base0 fp1 -∗ log_recs γ base0 fp2 -∗ ⌜ fp1 = fp2 ⌝.
Proof.
  iIntros (Hf1 Hf2) "#H1 #H2".
  pose proof Hf1 as (Hl1 & Hw1 & _). pose proof Hf2 as (Hl2 & Hw2 & _).
  iDestruct (log_recs_agree with "H1 H2") as %HRA.
  assert (Hb : ∀ fp, full_ok b fp →
            plog_term_at base0 fp b.(raft.entryID.index') = Some b.(raft.entryID.term')).
  { intros fp Hf. rewrite -(app_nil_r fp) (full_term_at b fp []) //. apply plog_term_at_base. }
  iDestruct (full_match _ _ _ b.(raft.entryID.index') Hw1 Hw2 with "H1 H2") as %Hm.
  { rewrite Hb //; by eexists. }
  { rewrite !Hb //. }
  iPureIntro. apply list_eq. intros k.
  destruct (fp1 !! k) as [e1|] eqn:He1; destruct (fp2 !! k) as [e2|] eqn:He2.
  - pose proof (Hw1 _ _ He1) as Hi1. pose proof (Hw2 _ _ He2) as Hi2.
    rewrite base0_index in Hi1 Hi2.
    apply lookup_lt_Some in He1 as Hk.
    assert (Ht : plog_term_at base0 fp1 (W64 (Z.of_nat k + 1)) = plog_term_at base0 fp2 (W64 (Z.of_nat k + 1))).
    { apply Hm. word. }
    rewrite (plog_term_at_lookup _ _ _ k e1) // in Ht; [|rewrite base0_index; word].
    rewrite (plog_term_at_lookup _ _ _ k e2) // in Ht; [|rewrite base0_index; word].
    injection Ht as Ht.
    destruct (HRA _ _ _ _ He1 He2 ltac:(rewrite base0_index; word) ltac:(rewrite base0_index; word) Ht
                ltac:(apply word.unsigned_inj; lia)) as [-> _].
    done.
  - apply lookup_lt_Some in He1. apply lookup_ge_None in He2. lia.
  - apply lookup_lt_Some in He2. apply lookup_ge_None in He1. lia.
  - done.
Qed.

(** Terms in a full log with records never go down. *)
Lemma recs_mono γ F :
  plog_wf base0 F →
  log_recs γ base0 F -∗
  ⌜ ∀ (j k x y : w64), uint.Z j ≤ uint.Z k →
      plog_term_at base0 F j = Some x → plog_term_at base0 F k = Some y →
      uint.Z x ≤ uint.Z y ⌝.
Proof.
  iIntros (Hwf) "#H".
  pose proof (plog_wf_range _ _ Hwf) as Hrng. rewrite /plog_last_index_Z base0_index in Hrng.
  iAssert (⌜ ∀ (k : nat) e, F !! k = Some e →
              ∃ pt, plog_term_at base0 F (W64 (Z.of_nat k)) = Some pt ∧
                    uint.Z pt ≤ uint.Z e.(raftpb.Entry.Term') ⌝)%I as %Hstep.
  { iIntros (k e Hk). apply lookup_lt_Some in Hk as Hlt.
    iDestruct (log_recs_lookup with "H") as (pt Hpt) "He"; [exact Hk|lia|].
    iDestruct (is_entry_r_pt with "He") as %Hle. iPureIntro. eauto. }
  iPureIntro.
  intros j k x y Hjk Hx Hy.
  remember (Z.to_nat (uint.Z k - uint.Z j)) as d eqn:Hd.
  revert k y Hjk Hy Hd. induction d as [|d IH]; intros k y Hjk Hy Hd.
  - assert (j = k) as -> by word. rewrite Hx in Hy. injection Hy as ->. lia.
  - (* the entry at [k] follows one whose term is at most its own *)
    pose proof (word.unsigned_range j).
    assert (Hk0 : 0 < uint.Z k) by lia.
    rewrite /plog_term_at base0_index in Hy.
    rewrite decide_False in Hy; [|lia]. rewrite decide_False in Hy; [|lia].
    destruct (F !! _) as [e|] eqn:He; [|done]. simpl in Hy. injection Hy as <-.
    destruct (Hstep _ _ He) as (pt & Hpt & Hle).
    set (k' := W64 (Z.of_nat (Z.to_nat (uint.Z k - 0 - 1)))) in *.
    assert (Hk' : uint.Z k' = uint.Z k - 1) by (subst k'; word).
    specialize (IH k' pt ltac:(lia) Hpt ltac:(lia)). lia.
Qed.

(** Walking down from an entry of term [T]: every entry of term [T] in a
    full log with records sits past the campaign log [F0] of [T]'s leader,
    and the one just past it follows [F0]'s last term. *)
Lemma recs_chain γ F ldr (T : w64) F0 :
  plog_wf base0 F →
  is_leader γ ldr T -∗ is_camp γ ldr T F0 -∗ log_recs γ base0 F -∗
  ⌜ ∀ k : w64, 0 < uint.Z k → plog_term_at base0 F k = Some T →
      plog_last_index_Z base0 F0 < uint.Z k ∧
      plog_term_at base0 F (W64 (plog_last_index_Z base0 F0))
        = Some (plog_last base0 F0).(raft.entryID.term') ∧
      ∀ j : w64, plog_last_index_Z base0 F0 < uint.Z j ≤ uint.Z k →
        plog_term_at base0 F j = Some T ⌝.
Proof.
  iIntros (Hwf) "#Hl #Hc #H".
  pose proof (plog_wf_range _ _ Hwf) as Hrng. rewrite /plog_last_index_Z base0_index in Hrng.
  set (L0 := plog_last_index_Z base0 F0).
  iAssert (⌜ ∀ (k : nat) e, F !! k = Some e → e.(raftpb.Entry.Term') = T →
              (L0 < Z.of_nat k + 1)%Z ∧
              ((Z.of_nat k + 1 = L0 + 1)%Z →
                 plog_term_at base0 F (W64 (Z.of_nat k)) = Some (plog_last base0 F0).(raft.entryID.term')) ∧
              ((L0 + 1 < Z.of_nat k + 1)%Z → plog_term_at base0 F (W64 (Z.of_nat k)) = Some T) ⌝)%I
    as %Hstep.
  { iIntros (k e Hk HT). apply lookup_lt_Some in Hk as Hlt.
    iDestruct (log_recs_lookup with "H") as (pt Hpt) "He"; [exact Hk|lia|].
    iDestruct "He" as (ldr' γt b l0 F0') "(#Hl' & _ & #Hc' & _ & %Hok)".
    rewrite HT. iDestruct (is_leader_unique with "Hl Hl'") as %<-.
    iDestruct (is_camp_agree with "Hc Hc'") as %<-.
    specialize (Hwf _ _ Hk). rewrite base0_index in Hwf.
    destruct Hok as (H1 & _ & H2 & H3). rewrite HT in H2 H3.
    iPureIntro. split_and!.
    - rewrite Hwf in H1. unfold L0. lia.
    - intros Heq. rewrite Hpt. f_equal. apply H2. unfold L0 in Heq. lia.
    - intros Hgt. rewrite Hpt. f_equal. apply H3. unfold L0 in Hgt. lia. }
  iPureIntro. intros k Hk0 Hk.
  remember (Z.to_nat (uint.Z k)) as d eqn:Hd.
  revert k Hk0 Hk Hd. induction d as [|d IH]; intros k Hk0 Hk Hd; [lia|].
  rewrite /plog_term_at base0_index in Hk.
  rewrite decide_False in Hk; [|lia]. rewrite decide_False in Hk; [|lia].
  destruct (F !! _) as [e|] eqn:He; [|done]. simpl in Hk. injection Hk as HT.
  destruct (Hstep _ _ He HT) as (HL & Hfirst & Hnext).
  rewrite Z2Nat.id in HL Hfirst Hnext; [|lia].
  assert (HkT : plog_term_at base0 F k = Some T).
  { rewrite /plog_term_at base0_index decide_False; [|lia]. rewrite decide_False; [|lia].
    rewrite He /= HT //. }
  split; [lia|].
  destruct (decide (uint.Z k = L0 + 1)) as [Hfst|Hfst].
  - specialize (Hfirst ltac:(lia)).
    split.
    + replace (W64 L0) with (W64 (uint.Z k - 0 - 1)) by (f_equal; lia). done.
    + intros j Hj. assert (j = k) as -> by word. done.
  - specialize (Hnext ltac:(lia)).
    pose proof (plog_last_index_Z_nonneg base0 F0).
    set (k' := W64 (uint.Z k - 0 - 1)).
    assert (Hk' : uint.Z k' = uint.Z k - 1) by (subst k'; word).
    destruct (IH k' ltac:(lia) Hnext ltac:(lia)) as (_ & Hb & Hall).
    split; [done|].
    intros j Hj. destruct (decide (uint.Z j = uint.Z k)) as [Hjk|Hjk].
    + assert (j = k) as -> by word. done.
    + apply Hall. lia.
Qed.

(** *** Leaders' full logs (2026-10-03)

    [lpfull γ ldr t bL l fp]: [fp] is the compacted prefix of [ldr]'s log
    [(bL, l)] in term [t], with records; the full log [fp ++ l] extends
    [ldr]'s campaign log of [t], is well-formed, and has no term above
    [t].  [lead_full γ t G]: [G] is the full log of a [lead_prefix] of
    [t]. *)

Definition lpfull γ (ldr t : w64) (bL : raft.entryID.t) (l fp : list raftpb.Entry.t)
  : iProp Σ :=
  ∃ F0, is_camp γ ldr t F0 ∗ log_recs γ base0 fp ∗
    ⌜ full_ok bL fp ∧ F0 `prefix_of` fp ++ l ∧ plog_wf bL l ∧
      ∀ (j x : w64), plog_term_at base0 (fp ++ l) j = Some x → uint.Z x ≤ uint.Z t ⌝.

Global Instance lpfull_pers γ ldr t bL l fp : Persistent (lpfull γ ldr t bL l fp).
Proof. apply _. Qed.
Global Instance lpfull_timeless γ ldr t bL l fp : Timeless (lpfull γ ldr t bL l fp).
Proof. apply _. Qed.

Definition lead_full γ (t : w64) (G : list raftpb.Entry.t) : iProp Σ :=
  ∃ ldr bL l fp, lead_prefix γ ldr t bL l ∗ lpfull γ ldr t bL l fp ∗ ⌜ G = fp ++ l ⌝.

Global Instance lead_full_pers γ t G : Persistent (lead_full γ t G).
Proof. apply _. Qed.
Global Instance lead_full_timeless γ t G : Timeless (lead_full γ t G).
Proof. apply _. Qed.

Lemma lead_full_intro γ ldr t bL l fp :
  lead_prefix γ ldr t bL l -∗ lpfull γ ldr t bL l fp -∗ lead_full γ t (fp ++ l).
Proof. iIntros "#H1 #H2". iExists ldr, bL, l, fp. iFrame "#". done. Qed.

Lemma lead_full_wf γ t G :
  lead_full γ t G -∗
  ⌜ plog_wf base0 G ∧ ∀ (j x : w64), plog_term_at base0 G j = Some x → uint.Z x ≤ uint.Z t ⌝ ∗
  log_recs γ base0 G.
Proof.
  iIntros "(%ldr & %bL & %l & %fp & #Hp & (%F0 & _ & #Hfr & %Hfull & _ & %Hwf & %Ht) & ->)".
  iDestruct (lead_prefix_wf with "Hp") as "[_ #Hr]".
  iSplit; [iPureIntro; split; [by eapply full_wf|done]|].
  iApply (log_recs_full with "Hfr Hr"). apply Hfull.
Qed.

Lemma lead_full_camp γ t G :
  lead_full γ t G -∗
  ∃ ldr F0, is_leader γ ldr t ∗ is_camp γ ldr t F0 ∗ ⌜ F0 `prefix_of` G ⌝.
Proof.
  iIntros "(%ldr & %bL & %l & %fp & (#Hl & _) & (%F0 & #Hc & _ & %Hfull & %Hpre & _) & ->)".
  iExists ldr, F0. iFrame "#". done.
Qed.

(** Two full logs of one term's leader agree wherever both have a term. *)
Lemma lead_full_agree γ t G1 G2 (j : w64) :
  is_Some (plog_term_at base0 G1 j) → is_Some (plog_term_at base0 G2 j) →
  lead_full γ t G1 -∗ lead_full γ t G2 -∗
  ⌜ plog_term_at base0 G1 j = plog_term_at base0 G2 j ⌝.
Proof.
  iIntros (Hs1 Hs2) "#H1 #H2".
  iDestruct (lead_full_wf with "H1") as "[[%Hw1 _] #Hr1]".
  iDestruct (lead_full_wf with "H2") as "[[%Hw2 _] #Hr2]".
  iDestruct "H1" as (ldr1 bL1 l1 fp1) "(#Hp1 & (%F1 & _ & _ & %Hf1 & _) & ->)".
  iDestruct "H2" as (ldr2 bL2 l2 fp2) "(#Hp2 & (%F2 & _ & _ & %Hf2 & _) & ->)".
  iDestruct (lead_prefix_base with "Hp1 Hp2") as %<-.
  set (bi := bL1.(raft.entryID.index')).
  destruct (decide (uint.Z bi ≤ uint.Z j)) as [Hge|Hlt].
  - rewrite (full_term_at bL1 fp1 l1 j) // in Hs1.
    rewrite (full_term_at bL1 fp2 l2 j) // in Hs2.
    rewrite (full_term_at bL1 fp1 l1 j) // (full_term_at bL1 fp2 l2 j) //.
    iApply (lead_prefix_agree with "Hp1 Hp2"); done.
  - (* below the base: both have the base's term at the base, and match down *)
    assert (Hb : plog_term_at base0 (fp1 ++ l1) bi = plog_term_at base0 (fp2 ++ l2) bi).
    { rewrite (full_term_at bL1 fp1 l1) // (full_term_at bL1 fp2 l2) //.
      rewrite !plog_term_at_base //. }
    iDestruct (full_match _ _ _ bi Hw1 Hw2 with "Hr1 Hr2") as %Hm.
    { rewrite (full_term_at bL1 fp1 l1) // plog_term_at_base. by eexists. }
    { done. }
    iPureIntro. apply Hm. lia.
Qed.

(** *** Commitment, naming the committed log (2026-10-03)

    [cq γ t n G]: a quorum acknowledged the leader of [t] up to at least
    [n], and [G], a full log of that leader, has an entry of term [t] at
    [n] -- what [step_commit] establishes.  [commit_in γ F c tm]: the full
    log [F] agrees, at [c], with such a [G] for some [t ≤ tm] with
    [c ≤ n].  A node keeps [commit_in] of its commit index; messages carry
    it of the [Commit] they report.  [is_committed γ i] forgets the log. *)

Definition cq γ (t n : w64) (G : list raftpb.Entry.t) : iProp Σ :=
  ⌜ plog_term_at base0 G n = Some t ⌝ ∗ lead_full γ t G ∗
  ∃ q, ⌜ is_quorum γ.(re_cfg) q ⌝ ∗
    [∗ set] v ∈ q, ∃ i', ⌜ uint.Z n ≤ uint.Z i' ⌝ ∗ is_acked γ v t i'.

Global Instance cq_pers γ t n G : Persistent (cq γ t n G).
Proof. apply _. Qed.
Global Instance cq_timeless γ t n G : Timeless (cq γ t n G).
Proof. apply _. Qed.

Definition commit_in γ (F : list raftpb.Entry.t) (c tm : w64) : iProp Σ :=
  ⌜ uint.Z c = 0 ⌝ ∨
  ∃ t n G, cq γ t n G ∗
    ⌜ uint.Z c ≤ uint.Z n ∧ uint.Z t ≤ uint.Z tm ∧
      plog_term_at base0 G c = plog_term_at base0 F c ⌝.

Global Instance commit_in_pers γ F c tm : Persistent (commit_in γ F c tm).
Proof. apply _. Qed.
Global Instance commit_in_timeless γ F c tm : Timeless (commit_in γ F c tm).
Proof. apply _. Qed.

Definition is_committed γ (i : w64) : iProp Σ :=
  ⌜ uint.Z i = 0 ⌝ ∨ ∃ t n G, ⌜ uint.Z i ≤ uint.Z n ⌝ ∗ cq γ t n G.

Global Instance is_committed_pers γ i : Persistent (is_committed γ i).
Proof. apply _. Qed.
Global Instance is_committed_timeless γ i : Timeless (is_committed γ i).
Proof. apply _. Qed.

Lemma is_committed_0 γ : ⊢ is_committed γ (W64 0).
Proof. iLeft. done. Qed.

(** What is committed up to [i] is committed up to anything below. *)
Lemma is_committed_le γ (i j : w64) :
  uint.Z j ≤ uint.Z i → is_committed γ i -∗ is_committed γ j.
Proof.
  iIntros (Hle) "[%H0 | (%t & %n & %G & %Hi & #Hq)]".
  - iLeft. iPureIntro. word.
  - iRight. iExists t, n, G. iFrame "Hq". iPureIntro. lia.
Qed.

Lemma commit_in_committed γ F c tm : commit_in γ F c tm -∗ is_committed γ c.
Proof.
  iIntros "[%H0 | (%t & %n & %G & #Hq & %Hc & _)]"; [by iLeft|].
  iRight. iExists t, n, G. iFrame "Hq". done.
Qed.

Lemma cq_full γ t n G :
  cq γ t n G -∗ ⌜ plog_wf base0 G ⌝ ∗ log_recs γ base0 G.
Proof.
  iIntros "(_ & #Hf & _)". iDestruct (lead_full_wf with "Hf") as "[[% _] $]". done.
Qed.

(** [commit_in] of a full log with records holds of anything below, and
    of any log that agrees with it at its commit point. *)
Lemma commit_in_le γ F (c c' tm : w64) :
  plog_wf base0 F → uint.Z c' ≤ uint.Z c →
  log_recs γ base0 F -∗ commit_in γ F c tm -∗ commit_in γ F c' tm.
Proof.
  iIntros (Hwf Hle) "#Hr [%H0 | (%t & %n & %G & #Hq & %Hc & %Ht & %Heq)]".
  { iLeft. iPureIntro. word. }
  iDestruct (cq_full with "Hq") as "[%HwG #HrG]".
  iPoseProof "Hq" as "(%Hn & _)".
  assert (HsG : is_Some (plog_term_at base0 G c)).
  { apply (full_term_at_some _ _ n); [by eexists|lia]. }
  iDestruct (full_match _ _ _ c HwG Hwf HsG Heq with "HrG Hr") as %Hm.
  iRight. iExists t, n, G. iFrame "Hq".
  iPureIntro. split_and!; [lia|done|]. apply Hm. lia.
Qed.

Lemma commit_in_agree γ F F' (c tm tm' : w64) :
  uint.Z tm ≤ uint.Z tm' →
  plog_term_at base0 F' c = plog_term_at base0 F c →
  commit_in γ F c tm -∗ commit_in γ F' c tm'.
Proof.
  iIntros (Htm Heq) "[%H0 | (%t & %n & %G & #Hq & %Hc & %Ht & %HG)]"; [by iLeft|].
  iRight. iExists t, n, G. iFrame "Hq". iPureIntro. split_and!; [done|lia|congruence].
Qed.

(** *** Histories of acknowledgements (2026-10-03)

    What Leader Completeness needs of a voter is that its log, at the
    moment it voted in [T], still agreed with every acknowledgement it had
    made in an earlier term [t] -- *unless* the leaders of the terms in
    between disagreed among themselves, which the induction over terms
    rules out.  [hist γ F t i B] says that of the full log [F] and an
    acknowledgement [(t, i)], for leaders of terms below [B]: at every
    index [j ≤ i], [F] has what some log [okL] -- of a leader of a term in
    [[t, B)], or a committed log of an earlier term -- has there; or two
    such logs already disagree at or below [j].  Each node keeps [hist] of
    each of its acknowledgements ([own_log_ghost]); the bound [B] is
    [bnd s] -- the current term, plus one when the node has a leader or
    is one. *)

Definition okL γ (t : w64) (B : Z) (j : w64) (X : list raftpb.Entry.t) : iProp Σ :=
  (∃ t'' : w64, ⌜ uint.Z t ≤ uint.Z t'' < B ⌝ ∗ lead_full γ t'' X) ∨
  (∃ t'' n'' : w64, ⌜ uint.Z t'' < uint.Z t ∧ uint.Z j ≤ uint.Z n'' ⌝ ∗ cq γ t'' n'' X).

Global Instance okL_pers γ t B j X : Persistent (okL γ t B j X).
Proof. apply _. Qed.

Definition hist γ (F : list raftpb.Entry.t) (t i : w64) (B : Z) : iProp Σ :=
  ∀ (j : w64) (_ : 0 < uint.Z j ≤ uint.Z i),
    (∃ X, okL γ t B j X ∗
       ⌜ is_Some (plog_term_at base0 X j) ∧ plog_term_at base0 X j = plog_term_at base0 F j ⌝) ∨
    (∃ (j' : w64) X1 X2, ⌜ uint.Z j' ≤ uint.Z j ⌝ ∗ okL γ t B j' X1 ∗ okL γ t B j' X2 ∗
       ⌜ is_Some (plog_term_at base0 X1 j') ∧ is_Some (plog_term_at base0 X2 j') ∧
         plog_term_at base0 X1 j' ≠ plog_term_at base0 X2 j' ⌝).

Global Instance hist_pers γ F t i B : Persistent (hist γ F t i B).
Proof. apply _. Qed.

Lemma okL_mono γ t B B' j X : B ≤ B' → okL γ t B j X -∗ okL γ t B' j X.
Proof.
  iIntros (HB) "[(%t'' & %Ht & #H) | H]"; [iLeft|by iRight].
  iExists t''. iFrame "H". iPureIntro. lia.
Qed.

Lemma okL_le γ t B j j' X : uint.Z j' ≤ uint.Z j → okL γ t B j X -∗ okL γ t B j' X.
Proof.
  iIntros (Hj) "[H | (%t'' & %n'' & %Ht & #H)]"; [by iLeft|iRight].
  iExists t'', n''. iFrame "H". iPureIntro. lia.
Qed.

Lemma hist_mono γ F t i B B' : B ≤ B' → hist γ F t i B -∗ hist γ F t i B'.
Proof.
  iIntros (HB) "#H %j %Hj". iDestruct ("H" $! j Hj) as "[(%X & #HX & %HXj) | (%j' & %X1 & %X2 & %Hj' & #H1 & #H2 & %Hd)]".
  - iLeft. iExists X. iFrame "%". iApply (okL_mono with "HX"); done.
  - iRight. iExists j', X1, X2. iFrame "%".
    iSplit; iApply (okL_mono with "[]"); done.
Qed.

(** A log that keeps every term [F] has keeps its histories. *)
Lemma hist_keep γ F F' t i B :
  (∀ j : w64, 0 < uint.Z j ≤ uint.Z i → is_Some (plog_term_at base0 F j) →
     plog_term_at base0 F' j = plog_term_at base0 F j) →
  hist γ F t i B -∗ hist γ F' t i B.
Proof.
  iIntros (Hk) "#H %j %Hj". iDestruct ("H" $! j Hj) as "[(%X & #HX & %Hs & %HXj) | Hc]"; [|by iRight].
  iLeft. iExists X. iFrame "HX". iPureIntro. split; [done|].
  rewrite HXj Hk //. by rewrite -HXj.
Qed.

(** A full log that agrees with [okL]-log [X] at [i] has a history of
    [(t, i)]. *)
Lemma hist_of_agree γ F X t i B :
  plog_wf base0 F →
  is_Some (plog_term_at base0 X i) → plog_term_at base0 X i = plog_term_at base0 F i →
  log_recs γ base0 F -∗ okL γ t B i X -∗ hist γ F t i B.
Proof.
  iIntros (HwF Hs Heq) "#HrF #HX %j %Hj". iLeft. iExists X.
  iAssert (⌜ plog_wf base0 X ⌝ ∗ log_recs γ base0 X)%I as "[%HwX #HrX]".
  { iDestruct "HX" as "[(% & _ & #Hf) | (% & % & _ & #Hq)]".
    - iDestruct (lead_full_wf with "Hf") as "[[% _] $]". done.
    - iApply (cq_full with "Hq"). }
  iDestruct (full_match _ _ _ i HwX HwF Hs Heq with "HrX HrF") as %Hm.
  iSplit; first (iApply (okL_le with "HX"); lia).
  iPureIntro. split; [apply (full_term_at_some _ _ i); [done|lia]|]. apply Hm. lia.
Qed.

(** *** Acknowledgements, justified

    [ack_agree γ b es t i]: the log [(b, es)] reaches [i] and has, at [i],
    the term some log of the leader of [t] has there.  [own_log_ghost]
    keeps it of every acknowledgement a non-leader has made in its current
    term above its commit index ([acks_ok]): that is what
    [heartbeat_commit_le_last] needs, and what a later [App]/[Snap] of the
    same term cannot undo -- they come from the same leader, so they agree
    with the log at and below [i] ([ack_agree_term]). *)

Definition ack_agree γ (b : raft.entryID.t) (es : list raftpb.Entry.t) (t i : w64)
  : iProp Σ :=
  ⌜ uint.Z i ≤ plog_last_index_Z b es ⌝ ∗
  ∃ ldr bL l, lead_prefix γ ldr t bL l ∗
    ⌜ is_Some (plog_term_at bL l i) ∧ plog_term_at bL l i = plog_term_at b es i ⌝ ∗
    ∃ fp, lpfull γ ldr t bL l fp.

Global Instance ack_agree_pers γ b es t i : Persistent (ack_agree γ b es t i).
Proof. apply _. Qed.
Global Instance ack_agree_timeless γ b es t i : Timeless (ack_agree γ b es t i).
Proof. apply _. Qed.

(** A log that agrees with the leader of [t] at [i] agrees, at and below
    [i], with every other log of that leader. *)
Lemma ack_agree_term γ b es t i ldr' bL l' (j : w64) :
  plog_wf_r b es →
  uint.Z b.(raft.entryID.index') ≤ uint.Z j → uint.Z bL.(raft.entryID.index') ≤ uint.Z j →
  uint.Z j ≤ uint.Z i →
  is_Some (plog_term_at bL l' j) →
  log_recs γ b es -∗ ack_agree γ b es t i -∗ lead_prefix γ ldr' t bL l' -∗
  ⌜ plog_term_at b es j = plog_term_at bL l' j ⌝.
Proof.
  iIntros (Hwf Hj1 Hj2 Hji Hs') "#Hr (%Hi & %ldr & %bL0 & %l & #Hp & [%Hs %Heq] & _) #Hp'".
  iDestruct (lead_prefix_base with "Hp Hp'") as %->.
  iDestruct (lead_prefix_wf with "Hp") as "[%Hwfl #Hrl]".
  iDestruct (log_recs_agree with "Hr Hrl") as %HRA.
  assert (Hsi : is_Some (plog_term_at b es i)) by (rewrite -Heq //).
  pose proof (plog_match_down b es bL l i Hwf Hwfl HRA Hsi (eq_sym Heq) j Hj1 Hj2 Hji) as Hj.
  assert (Hsl : is_Some (plog_term_at bL l j)).
  { destruct Hs as [x Hx]. apply plog_term_at_in_range.
    pose proof (plog_term_at_Some_range _ _ _ _ Hx). lia. }
  iDestruct (lead_prefix_agree _ _ _ _ _ l l' j Hsl Hs' with "Hp Hp'") as %Hj'.
  iPureIntro. by rewrite Hj Hj'.
Qed.

(** *** Messages *)

Definition is_message γ (m : msg.t) : iProp Σ :=
  match m.(msg.ty) with
  | mtype.Vote =>
      (* the candidate's campaign record, whose last entry the request
         reports (2026-10-03) *)
      ∃ Fc, is_camp γ m.(msg.from) m.(msg.term) Fc ∗
        ⌜ plog_last base0 Fc = raft.entryID.mk m.(msg.logterm) m.(msg.index) ⌝
  | mtype.VoteResp =>
      if m.(msg.reject) then True%I
      else is_vote γ m.(msg.from) m.(msg.term) m.(msg.to)
  | mtype.App =>
      ⌜ app_payload_ok m ⌝ ∗
      is_leader γ m.(msg.from) m.(msg.term) ∗
      (* the leader's log [l] has [(logterm, index)] and the entries after;
         its full log agrees with a committed log at [Commit] *)
      (∃ bL l fp, lead_prefix γ m.(msg.from) m.(msg.term) bL l ∗
         ⌜ plog_term_at bL l m.(msg.index) = Some m.(msg.logterm) ∧
           m.(msg.entries) `prefix_of` plog_from bL l (word.add m.(msg.index) (W64 1)) ⌝ ∗
         lpfull γ m.(msg.from) m.(msg.term) bL l fp ∗
         commit_in γ (fp ++ l) m.(msg.commit) m.(msg.term)) ∗
      ⌜ m.(msg.from) ≠ W64 0 ⌝
  | mtype.AppResp =>
      if m.(msg.reject) then True%I
      else is_acked γ m.(msg.from) m.(msg.term) m.(msg.index)
  | mtype.Heartbeat =>
      is_leader γ m.(msg.from) m.(msg.term) ∗
      (∃ Fl, lead_full γ m.(msg.term) Fl ∗ commit_in γ Fl m.(msg.commit) m.(msg.term)) ∗
      (* [Commit ≤ pr.Match], which the receiver acknowledged *)
      (∃ i, ⌜ uint.Z m.(msg.commit) ≤ uint.Z i ⌝ ∗ is_acked γ m.(msg.to) m.(msg.term) i) ∗
      ⌜ m.(msg.from) ≠ W64 0 ⌝
  | mtype.Snap =>
      (* the leader's, of a committed prefix ending in a real entry *)
      is_leader γ m.(msg.from) m.(msg.term) ∗
      is_snap_meta γ m.(msg.logterm) m.(msg.index) ∗
      (* the leader's log has the snapshot's last entry *)
      (∃ bL l fp, lead_prefix γ m.(msg.from) m.(msg.term) bL l ∗
         ⌜ plog_term_at bL l m.(msg.index) = Some m.(msg.logterm) ⌝ ∗
         lpfull γ m.(msg.from) m.(msg.term) bL l fp ∗
         commit_in γ (fp ++ l) m.(msg.index) m.(msg.term)) ∗
      ⌜ m.(msg.from) ≠ W64 0 ⌝
  | _ => True%I
  end.

Global Instance is_message_pers γ m : Persistent (is_message γ m).
Proof.
  rewrite /is_message. destruct (m.(msg.ty)), (m.(msg.reject)); apply _.
Qed.
Global Instance is_message_timeless γ m : Timeless (is_message γ m).
Proof.
  rewrite /is_message. destruct (m.(msg.ty)), (m.(msg.reject)); apply _.
Qed.

(** The message types that carry nothing. *)
Definition msg_free (ty : mtype.t) : bool :=
  match ty with
  | mtype.HeartbeatResp | mtype.Propose | mtype.PreVote
  | mtype.PreVoteResp | mtype.ReadIndex | mtype.ReadIndexResp => true
  | _ => false
  end.

Lemma is_message_free γ m : msg_free m.(msg.ty) = true → ⊢ is_message γ m.
Proof.
  rewrite /is_message. intros Hty. destruct (m.(msg.ty)); try discriminate; done.
Qed.

(** A *rejecting* [VoteResp] is free too: it reports no vote. *)
Lemma is_message_reject γ (from to term : w64) :
  ⊢ is_message γ (msg.plain mtype.VoteResp from to term true).
Proof. rewrite /is_message /=. done. Qed.

(** A granting [VoteResp] carries the vote it reports, and nothing else. *)
Lemma is_message_grant γ (from to term : w64) :
  is_vote γ from term to ⊢ is_message γ (msg.plain mtype.VoteResp from to term false).
Proof. by rewrite /is_message /=. Qed.

Lemma is_message_grant_inv γ m :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.reject) = false →
  is_message γ m -∗ is_vote γ m.(msg.from) m.(msg.term) m.(msg.to).
Proof. intros Hty Hrej. rewrite /is_message Hty Hrej. by iIntros "$". Qed.

(** *** A node's protocol state *)

Definition vote_hist_ok (voted : gmap w64 w64) (s : pstate.t) : Prop :=
  (∀ t, is_Some (voted !! t) → uint.Z t ≤ uint.Z s.(pstate.term)) ∧
  voted !! s.(pstate.term) =
    (if decide (s.(pstate.vote) = W64 0) then None else Some s.(pstate.vote)).

(** [pbecome_follower] keeps the vote only when the term does not move. *)
Local Lemma pbecome_follower_vote_ne s term lead :
  term ≠ s.(pstate.term) → (pbecome_follower s term lead).(pstate.vote) = W64 0.
Proof. intros Hne. rewrite /pbecome_follower /=. rewrite decide_False //. Qed.

Local Lemma pbecome_follower_vote_same s lead :
  (pbecome_follower s s.(pstate.term) lead).(pstate.vote) = s.(pstate.vote).
Proof. rewrite /pbecome_follower /=. rewrite decide_True //. Qed.

(** A term the node has not reached yet is free to vote in. *)
Lemma vote_hist_fresh voted s t :
  vote_hist_ok voted s →
  uint.Z s.(pstate.term) < uint.Z t →
  voted !! t = None.
Proof.
  intros [Hdom _] Hlt. destruct (voted !! t) eqn:Ht; last done.
  exfalso. unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
Qed.

(** [vote_hist_ok] reads only [term] and [vote]. *)
Local Lemma vote_hist_ok_eq voted s1 s2 :
  vote_hist_ok voted s1 →
  s2.(pstate.term) = s1.(pstate.term) →
  s2.(pstate.vote) = s1.(pstate.vote) →
  vote_hist_ok voted s2.
Proof. rewrite /vote_hist_ok. intros H -> ->. exact H. Qed.

Definition leader_wit γ id s : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader => is_leader γ id s.(pstate.term)
  | _ => True%I
  end.

Global Instance leader_wit_pers γ id s : Persistent (leader_wit γ id s).
Proof. rewrite /leader_wit. destruct (s.(pstate.role)); apply _. Qed.
Global Instance leader_wit_timeless γ id s : Timeless (leader_wit γ id s).
Proof. rewrite /leader_wit. destruct (s.(pstate.role)); apply _. Qed.

(** The terms a node has allocated a term log for: ones it has left behind,
    or the current one if it is leader in it. *)
(** What a node's term map holds: [is_term_log]'s triple. *)
Notation term_rec := (gname * raft.entryID.t * list raftpb.Entry.t)%type.

Definition terms_ok (terms : gmap w64 term_rec) (s : pstate.t) : Prop :=
  ∀ t, is_Some (terms !! t) →
    uint.Z t < uint.Z s.(pstate.term) ∨
    (t = s.(pstate.term) ∧ s.(pstate.role) = role.Leader).

(** A leader owns the term log of its term, whose recorded base and initial
    log are the leader's base and a prefix of its log, and holds a fragment
    of it for every entry it has created since ([lead_frags]). *)
Definition lead_log_own γ (s : pstate.t) (terms : gmap w64 term_rec) : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader =>
      ∃ γt (M : gmap w64 (raftpb.Entry.t * w64)) l0,
        ⌜ terms !! s.(pstate.term) = Some (γt, s.(pstate.base), l0) ⌝ ∗
        ghost_map_auth γt 1 M ∗
        ([∗ map] i ↦ e ∈ M, i ↪[γt]□ e) ∗
        (* nothing in the term log is past the leader's last index: what
           makes [step_propose]'s new indices fresh *)
        ⌜ ∀ i, is_Some (M !! i) → uint.Z i ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) ⌝ ∗
        ⌜ l0 `prefix_of` s.(pstate.log) ⌝ ∗
        lead_frags γt l0 s.(pstate.log)
  | _ => True%I
  end.

Global Instance lead_log_own_timeless γ s terms : Timeless (lead_log_own γ s terms).
Proof. rewrite /lead_log_own. destruct (s.(pstate.role)); apply _. Qed.

(** A leader's [Match] values are backed by acknowledgements. *)
Definition matched_ok γ (s : pstate.t) : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader => [∗ map] v ↦ i ∈ s.(pstate.matched), is_acked γ v s.(pstate.term) i
  | _ => True%I
  end.

Global Instance matched_ok_pers γ s : Persistent (matched_ok γ s).
Proof. rewrite /matched_ok. destruct (s.(pstate.role)); apply _. Qed.
Global Instance matched_ok_timeless γ s : Timeless (matched_ok γ s).
Proof. rewrite /matched_ok. destruct (s.(pstate.role)); apply _. Qed.

(** The log's shape: well-formed (in range), and [base ≤ commit ≤
    lastIndex()]. *)
Definition log_ok (s : pstate.t) : Prop :=
  plog_wf_r s.(pstate.base) s.(pstate.log) ∧
  uint.Z s.(pstate.base).(raft.entryID.index') ≤ uint.Z s.(pstate.commit) ∧
  uint.Z s.(pstate.commit) ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log).

(** A node acknowledges only at its own term. *)
Definition acks_term (s : pstate.t) (acks : gmap (w64 * w64) unit) : Prop :=
  ∀ k, is_Some (acks !! k) → uint.Z k.1 ≤ uint.Z s.(pstate.term).

(** An acknowledgement of the current term above the commit index is
    justified by the log ([ack_agree]).  Only of a non-leader: a leader's
    log does not shrink, and it leaves its term only for a higher one. *)
Definition ack_ok γ (s : pstate.t) (k : w64 * w64) : iProp Σ :=
  ∀ _ : k.1 = s.(pstate.term) ∧ uint.Z s.(pstate.commit) < uint.Z k.2,
    ack_agree γ s.(pstate.base) s.(pstate.log) k.1 k.2.

Global Instance ack_ok_pers γ s k : Persistent (ack_ok γ s k).
Proof. apply _. Qed.
Global Instance ack_ok_timeless γ s k : Timeless (ack_ok γ s k).
Proof. apply _. Qed.

Definition acks_ok γ (s : pstate.t) (acks : gmap (w64 * w64) unit) : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader => True
  | _ => [∗ map] k ↦ _ ∈ acks, ack_ok γ s k
  end.

Global Instance acks_ok_pers γ s acks : Persistent (acks_ok γ s acks).
Proof. rewrite /acks_ok. destruct (s.(pstate.role)); apply _. Qed.
Global Instance acks_ok_timeless γ s acks : Timeless (acks_ok γ s acks).
Proof. rewrite /acks_ok. destruct (s.(pstate.role)); apply _. Qed.

(** *** The history invariants (2026-10-03)

    [bnd s]: the terms whose leaders a node's histories ([hist]) may
    mention -- those below its term, and its term itself once it has a
    leader or is one.  It never decreases, and it is the node's term
    exactly when it can cast a first vote ([pcan_vote] with no vote and no
    leader), which is what a vote records ([vlogs_ok]). *)
Definition bnd (s : pstate.t) : Z :=
  if decide (s.(pstate.lead) = W64 0 ∧ s.(pstate.role) ≠ role.Leader)
  then uint.Z s.(pstate.term) else uint.Z s.(pstate.term) + 1.

(** No term in a node's full log is above its own; a candidate has none
    of its own term either. *)
Definition terms_le (s : pstate.t) (F : list raftpb.Entry.t) : Prop :=
  ∀ (j x : w64), plog_term_at base0 F j = Some x →
    uint.Z x ≤ uint.Z s.(pstate.term) ∧
    (s.(pstate.role) = role.Candidate → uint.Z x < uint.Z s.(pstate.term)).

(** A candidate's full log is its campaign record; a leader's extends it,
    by at least the leader's entry, and ends in an entry of its term. *)
Definition camp_own γ (id : w64) (s : pstate.t) (F : list raftpb.Entry.t) : iProp Σ :=
  match s.(pstate.role) with
  | role.Candidate => is_camp γ id s.(pstate.term) F
  | role.Leader => ∃ F0, is_camp γ id s.(pstate.term) F0 ∗
       ⌜ F0 `prefix_of` F ∧ plog_last_index_Z base0 F0 < plog_last_index_Z base0 F ∧
         (plog_last base0 F).(raft.entryID.term') = s.(pstate.term) ⌝
  | role.Follower => True
  end.

Global Instance camp_own_pers γ id s F : Persistent (camp_own γ id s F).
Proof. rewrite /camp_own. destruct (s.(pstate.role)); apply _. Qed.
Global Instance camp_own_timeless γ id s F : Timeless (camp_own γ id s F).
Proof. rewrite /camp_own. destruct (s.(pstate.role)); apply _. Qed.

(** Node [v]'s [k]-th vote-time log: it voted in [T] with full log [F]. *)
Definition is_vlog γ (v : w64) (k : nat) (T : w64) (F : list raftpb.Entry.t) : iProp Σ :=
  ∃ γl, ⌜ γ.(re_vlogs) !! v = Some γl ⌝ ∗ k ↪[γl]□ (T, F).

Global Instance is_vlog_pers γ v k T F : Persistent (is_vlog γ v k T F).
Proof. apply _. Qed.
Global Instance is_vlog_timeless γ v k T F : Timeless (is_vlog γ v k T F).
Proof. apply _. Qed.

(** A vote-time log has the history of every acknowledgement of an
    earlier term (all of them were made before the vote: a node
    acknowledges only at its own term). *)
Definition vlogs_ok γ (s : pstate.t) (acks : gmap (w64 * w64) unit)
    (vlogs : gmap nat (w64 * list raftpb.Entry.t)) : iProp Σ :=
  [∗ map] x ∈ vlogs, ⌜ uint.Z x.1 ≤ uint.Z s.(pstate.term) ⌝ ∗
    [∗ map] k ↦ _ ∈ acks, ∀ _ : uint.Z k.1 < uint.Z x.1, hist γ x.2 k.1 k.2 (uint.Z x.1).

Global Instance vlogs_ok_pers γ s acks vlogs : Persistent (vlogs_ok γ s acks vlogs).
Proof. apply _. Qed.

Definition hists_ok γ (s : pstate.t) (F : list raftpb.Entry.t)
    (acks : gmap (w64 * w64) unit) : iProp Σ :=
  [∗ map] k ↦ _ ∈ acks, hist γ F k.1 k.2 (bnd s).

Global Instance hists_ok_pers γ s F acks : Persistent (hists_ok γ s F acks).
Proof. apply _. Qed.

(** What a vote of [v] for [c] in [T] records: [v]'s full log [Fv] then
    ([is_vlog]), with records, and that [c]'s campaign log was at least as
    up to date ([step_grant_vote]'s premise). *)
Definition vote_just γ (v T c : w64) : iProp Σ :=
  ∃ k Fv Fc, is_vlog γ v k T Fv ∗ is_camp γ c T Fc ∗ log_recs γ base0 Fv ∗
    ⌜ plog_wf base0 Fv ∧ plog_up_to_date base0 Fv (plog_last base0 Fc) = true ⌝.

Global Instance vote_just_pers γ v T c : Persistent (vote_just γ v T c).
Proof. apply _. Qed.
Global Instance vote_just_timeless γ v T c : Timeless (vote_just γ v T c).
Proof. apply _. Qed.

Definition own_log_ghost γ (id : w64) (s : pstate.t) : iProp Σ :=
  ∃ γm terms γa (acks : gmap (w64 * w64) unit) fp γc
    (camps : gmap w64 (list raftpb.Entry.t)) γl (vlogs : gmap nat (w64 * list raftpb.Entry.t)),
    "%Htname"  ∷ ⌜ γ.(re_terms) !! id = Some γm ⌝ ∗
    "Hterms"   ∷ ghost_map_auth γm 1 terms ∗
    "#Htfrags" ∷ ([∗ map] t ↦ γt ∈ terms, t ↪[γm]□ γt) ∗
    "%Hterms_ok" ∷ ⌜ terms_ok terms s ⌝ ∗
    "Htlog"    ∷ lead_log_own γ s terms ∗
    "%Haname"  ∷ ⌜ γ.(re_acks) !! id = Some γa ⌝ ∗
    "Hacks"    ∷ ghost_map_auth γa 1 acks ∗
    "#Hafrags" ∷ ([∗ map] k ↦ u ∈ acks, k ↪[γa]□ u) ∗
    "%Hacks_term" ∷ ⌜ acks_term s acks ⌝ ∗
    "#Hacks_ok" ∷ acks_ok γ s acks ∗
    "%Hlog_ok" ∷ ⌜ log_ok s ⌝ ∗
    "#Hrecs"   ∷ log_recs γ s.(pstate.base) s.(pstate.log) ∗
    "#Hmatched" ∷ matched_ok γ s ∗
    "#Hcommit" ∷ commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term) ∗
    "#Hbase"   ∷ base_ok γ s.(pstate.base) ∗
    (* 2026-10-03: the full log, campaign records, vote-time logs and the
       histories of acknowledgements *)
    "%Hfull"   ∷ ⌜ full_ok s.(pstate.base) fp ∧ plog_wf s.(pstate.base) s.(pstate.log) ∧
                   terms_le s (fp ++ s.(pstate.log)) ⌝ ∗
    "#Hfrecs"  ∷ log_recs γ base0 fp ∗
    "%Hcname"  ∷ ⌜ γ.(re_camp) !! id = Some γc ⌝ ∗
    "Hcamps"   ∷ ghost_map_auth γc 1 camps ∗
    "%Hcamps_ok" ∷ ⌜ ∀ T, is_Some (camps !! T) → uint.Z T ≤ uint.Z s.(pstate.term) ⌝ ∗
    "#Hcown"   ∷ camp_own γ id s (fp ++ s.(pstate.log)) ∗
    "%Hlname"  ∷ ⌜ γ.(re_vlogs) !! id = Some γl ⌝ ∗
    "Hvlogs"   ∷ ghost_map_auth γl 1 vlogs ∗
    "#Hvlogs_ok" ∷ vlogs_ok γ s acks vlogs ∗
    "#Hhists"  ∷ hists_ok γ s (fp ++ s.(pstate.log)) acks.

Global Instance own_log_ghost_timeless γ id s : Timeless (own_log_ghost γ id s).
Proof. apply _. Qed.

(** A role other than follower has voted for itself; a candidate has no
    leader.  (Invariants of every reachable state, 2026-10-03: what makes
    [bnd] never decrease and a first vote happen at [bnd s = term].) *)
Definition role_ok (id : w64) (s : pstate.t) : Prop :=
  (s.(pstate.role) ≠ role.Follower → s.(pstate.vote) = id) ∧
  (s.(pstate.role) = role.Candidate → s.(pstate.lead) = W64 0).

Definition own_raft_ghost γ (id : w64) (s : pstate.t) : iProp Σ :=
  ∃ γv voted,
    "%Hname"  ∷ ⌜ γ.(re_votes) !! id = Some γv ⌝ ∗
    "%Hidnz"  ∷ ⌜ id ≠ W64 0 ⌝ ∗
    "Hvoted"  ∷ ghost_map_auth γv 1 voted ∗
    "%Hhist"  ∷ ⌜ vote_hist_ok voted s ⌝ ∗
    "#Hfrags" ∷ ([∗ map] t ↦ c ∈ voted, is_vote γ id t c) ∗
    "#Hout"   ∷ ([∗ list] m ∈ s.(pstate.outbox), is_message γ m) ∗
    "#Htally" ∷ ([∗ set] v ∈ granted s.(pstate.votes), is_vote γ v s.(pstate.term) id) ∗
    "#Hlead"  ∷ leader_wit γ id s ∗
    "Hlg"     ∷ own_log_ghost γ id s ∗
    "%Hlead_ok" ∷ ⌜ lead_ok id s ⌝ ∗
    "%Hfollower_votes" ∷ ⌜ follower_votes_ok s ⌝ ∗
    "#Hvrecs" ∷ ([∗ map] t ↦ c ∈ voted, vote_just γ id t c) ∗
    "%Hrole_ok" ∷ ⌜ role_ok id s ⌝.

Global Instance own_raft_ghost_timeless γ id s : Timeless (own_raft_ghost γ id s).
Proof. apply _. Qed.

Lemma own_raft_ghost_intro γ id s γv voted :
  γ.(re_votes) !! id = Some γv →
  id ≠ W64 0 →
  ghost_map_auth γv 1 voted -∗
  ⌜ vote_hist_ok voted s ⌝ -∗
  ([∗ map] t ↦ c ∈ voted, is_vote γ id t c) -∗
  ([∗ list] m ∈ s.(pstate.outbox), is_message γ m) -∗
  ([∗ set] v ∈ granted s.(pstate.votes), is_vote γ v s.(pstate.term) id) -∗
  leader_wit γ id s -∗
  own_log_ghost γ id s -∗
  ⌜ lead_ok id s ⌝ -∗
  ⌜ follower_votes_ok s ⌝ -∗
  ([∗ map] t ↦ c ∈ voted, vote_just γ id t c) -∗
  ⌜ role_ok id s ⌝ -∗
  own_raft_ghost γ id s.
Proof.
  iIntros (??) "H1 %H2 #H3 #H4 #H5 #H6 H7 %H8 %H9 #H10 %H11". iExists γv, voted. by iFrame "∗#%".
Qed.

(** A non-leader does not record itself as leader. *)
Lemma own_raft_ghost_lead_ok γ id s :
  own_raft_ghost γ id s -∗ ⌜ lead_ok id s ⌝.
Proof. iIntros "H". iNamed "H". done. Qed.

(** A follower's tally is empty. *)
Lemma own_raft_ghost_follower_votes γ id s :
  own_raft_ghost γ id s -∗ ⌜ follower_votes_ok s ⌝.
Proof. iIntros "H". iNamed "H". done. Qed.

Lemma matched_ok_eq γ s1 s2 :
  s2.(pstate.role) = s1.(pstate.role) →
  s2.(pstate.term) = s1.(pstate.term) →
  s2.(pstate.matched) = s1.(pstate.matched) →
  matched_ok γ s1 -∗ matched_ok γ s2.
Proof. intros H1 H2 H3. rewrite /matched_ok H1 H2 H3. auto. Qed.

Lemma own_raft_ghost_excl γ id s1 s2 :
  own_raft_ghost γ id s1 -∗ own_raft_ghost γ id s2 -∗ False.
Proof.
  iIntros "(%γ1 & %v1 & %Hn1 & _ & H1 & _) (%γ2 & %v2 & %Hn2 & _ & H2 & _)".
  rewrite Hn1 in Hn2. injection Hn2 as <-.
  iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[Hq _].
  exfalso. by apply Qp.not_add_le_l in Hq.
Qed.

(** Everything in a node's outbox was legitimately put there. *)
Lemma own_raft_ghost_outbox γ id s :
  own_raft_ghost γ id s -∗ ([∗ list] m ∈ s.(pstate.outbox), is_message γ m).
Proof. iIntros "(% & % & _ & _ & _ & _ & _ & #H & _)". iFrame "#". Qed.

Lemma own_raft_ghost_is_leader γ id s :
  s.(pstate.role) = role.Leader →
  own_raft_ghost γ id s -∗ is_leader γ id s.(pstate.term).
Proof.
  iIntros (Hrole) "(% & % & _ & _ & _ & _ & _ & _ & _ & #H & _)".
  rewrite /leader_wit Hrole. iFrame "#".
Qed.

(** *** Pure facts about the vote tally *)

Lemma elem_of_granted (votes : gmap w64 bool) v :
  v ∈ granted votes ↔ votes !! v = Some true.
Proof.
  rewrite /granted elem_of_dom. split.
  - intros [b Hb]. apply map_lookup_filter_Some in Hb as [Hv Hb].
    simpl in Hb. by subst.
  - intros Hv. eexists. apply map_lookup_filter_Some. done.
Qed.

Lemma granted_empty : granted ∅ = ∅.
Proof. rewrite /granted map_filter_empty dom_empty_L //. Qed.

Lemma elem_of_granted_record_vote votes from b v :
  v ∈ granted (record_vote votes from b) →
  v ∈ granted votes ∨ (v = from ∧ b = true).
Proof.
  rewrite /record_vote. destruct (votes !! from) eqn:Hf; first by left.
  rewrite !elem_of_granted. destruct (decide (v = from)) as [->|Hne].
  - rewrite lookup_insert_eq. intros [= ->]. by right.
  - assert (Hne' : from ≠ v) by congruence.
    rewrite lookup_insert_ne //. by left.
Qed.

(** *** The log ghost state across a step *)

(** [acks_ok] across a step that never lowers the term or the commit index
    and demotes a leader only into a higher term.  Within one term the
    caller says how a justification survives the new log ([Hkeep]); across
    a term change there is nothing to keep: nothing of the new term has
    been acknowledged yet ([acks_term]). *)
Lemma acks_ok_upd γ s s' acks :
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  uint.Z s.(pstate.commit) ≤ uint.Z s'.(pstate.commit) →
  acks_term s acks →
  □ (⌜ s'.(pstate.term) = s.(pstate.term) ⌝ -∗ ∀ i,
       ⌜ uint.Z s'.(pstate.commit) < uint.Z i ⌝ -∗
       ack_agree γ s.(pstate.base) s.(pstate.log) s.(pstate.term) i -∗
       ack_agree γ s'.(pstate.base) s'.(pstate.log) s.(pstate.term) i) -∗
  acks_ok γ s acks -∗ acks_ok γ s' acks.
Proof.
  iIntros (Hle Hdown Hcm Hat) "#Hkeep #Hok".
  rewrite /acks_ok.
  destruct (s'.(pstate.role)) eqn:Hr'; [| |done].
  all: iApply big_sepM_intro; iIntros "!> %k %u %Hk" ([Hk1 Hk2]).
  all: pose proof (Hat k ltac:(by eexists)) as Hkt.
  all: destruct (decide (s'.(pstate.term) = s.(pstate.term))) as [Heq|Hne];
    [|exfalso; assert (uint.Z s.(pstate.term) ≠ uint.Z s'.(pstate.term))
         by (intros ?; apply Hne; by apply word.unsigned_inj);
       rewrite Hk1 in Hkt; lia].
  all: destruct (s.(pstate.role)) eqn:Hr;
    [ | | exfalso; specialize (Hdown ltac:(congruence) eq_refl); rewrite Heq in Hdown; lia].
  all: iDestruct (big_sepM_lookup with "Hok") as "Hk"; first exact Hk.
  all: assert (Hd : k.1 = s.(pstate.term) ∧ uint.Z s.(pstate.commit) < uint.Z k.2)
         by (split; [congruence|lia]).
  all: iSpecialize ("Hk" $! Hd).
  all: rewrite Hk1 Heq; iApply ("Hkeep" with "[//] [%] Hk"); lia.
Qed.

(** The log part of the ghost state across a step that does not make the
    node leader, or keeps it leader in the same term with the same log.  A
    leader that stops being one must have moved to a higher term: that is
    what keeps it from ever allocating a second term log for one term, and
    what makes its acknowledgements need no justification.  The caller
    supplies the new state's records, [Match] and commit facts, and how
    the justification of an acknowledgement survives ([acks_ok_upd]). *)
Lemma own_log_ghost_upd γ id s s' :
  (s'.(pstate.role) = role.Leader →
     s.(pstate.role) = role.Leader ∧ s'.(pstate.term) = s.(pstate.term) ∧
     s'.(pstate.base) = s.(pstate.base) ∧ s'.(pstate.log) = s.(pstate.log)) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  (s'.(pstate.role) = role.Candidate →
     s.(pstate.role) = role.Candidate ∧ s'.(pstate.term) = s.(pstate.term)) →
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  uint.Z s.(pstate.commit) ≤ uint.Z s'.(pstate.commit) →
  bnd s ≤ bnd s' →
  log_ok s' →
  own_log_ghost γ id s -∗
  □ (⌜ s'.(pstate.term) = s.(pstate.term) ⌝ -∗ ∀ i,
       ⌜ uint.Z s'.(pstate.commit) < uint.Z i ⌝ -∗
       ack_agree γ s.(pstate.base) s.(pstate.log) s.(pstate.term) i -∗
       ack_agree γ s'.(pstate.base) s'.(pstate.log) s.(pstate.term) i) -∗
  log_recs γ s'.(pstate.base) s'.(pstate.log) -∗
  matched_ok γ s' -∗
  base_ok γ s'.(pstate.base) -∗
  (∀ fp, ⌜ full_ok s.(pstate.base) fp ∧ plog_wf s.(pstate.base) s.(pstate.log) ∧
           terms_le s (fp ++ s.(pstate.log)) ⌝ -∗
     log_recs γ base0 fp -∗
     commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term) -∗
     ∃ fp', ⌜ (full_ok s'.(pstate.base) fp' ∧ plog_wf s'.(pstate.base) s'.(pstate.log) ∧
               terms_le s' (fp' ++ s'.(pstate.log))) ∧
              (s'.(pstate.role) ≠ role.Follower → fp' ++ s'.(pstate.log) = fp ++ s.(pstate.log)) ⌝ ∗
       log_recs γ base0 fp' ∗
       commit_in γ (fp' ++ s'.(pstate.log)) s'.(pstate.commit) s'.(pstate.term) ∗
       □ (∀ t i, ⌜ uint.Z t ≤ uint.Z s.(pstate.term) ⌝ -∗
            hist γ (fp ++ s.(pstate.log)) t i (bnd s) -∗
            hist γ (fp' ++ s'.(pstate.log)) t i (bnd s'))) -∗
  own_log_ghost γ id s'.
Proof.
  iIntros (Hlead Hdown Hcand Hle Hcm Hbnd Hok') "H #Hkeep #Hr' #Hm' #Hb' Hnew".
  iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  iDestruct ("Hnew" $! fp with "[%] Hfrecs Hcommit")
    as (fp' [Hfull' Hfeq]) "(#Hfr' & #Hc' & #Hh)"; first done.
  iDestruct (acks_ok_upd _ s s' acks Hle Hdown Hcm Hacks_term with "Hkeep Hacks_ok")
    as "#Hacks'".
  assert (Hterms_ok' : terms_ok terms s').
  { intros t Ht. destruct (Hterms_ok t Ht) as [Hlt | [-> Hr]].
    - left. lia.
    - destruct (decide (s'.(pstate.role) = role.Leader)) as [Hr'|Hr'].
      + destruct (Hlead Hr') as (_ & -> & _). by right.
      + left. by apply Hdown. }
  assert (Hacks_term' : acks_term s' acks).
  { intros k Hk. specialize (Hacks_term k Hk). lia. }
  assert (Hcamps_ok' : ∀ T, is_Some (camps !! T) → uint.Z T ≤ uint.Z s'.(pstate.term)).
  { intros T HT. specialize (Hcamps_ok T HT). lia. }
  iAssert (lead_log_own γ s' terms) with "[Htlog]" as "Htlog".
  { rewrite /lead_log_own.
    destruct (decide (s'.(pstate.role) = role.Leader)) as [Hr'|Hr'].
    - destruct (Hlead Hr') as (Hr & Ht & Hb & Hl).
      iEval (rewrite /lead_log_own Hr) in "Htlog". rewrite Hr' Ht Hb Hl. iExact "Htlog".
    - destruct (s'.(pstate.role)); [done|done|congruence]. }
  iAssert (camp_own γ id s' (fp' ++ s'.(pstate.log))) as "#Hcown'".
  { rewrite /camp_own. destruct (s'.(pstate.role)) eqn:Hr'; [done| |].
    - destruct (Hcand eq_refl) as [Hr Ht]. rewrite Hfeq; [|discriminate].
      iEval (rewrite /camp_own Hr) in "Hcown". rewrite Ht. iExact "Hcown".
    - destruct (Hlead eq_refl) as (Hr & Ht & _). rewrite Hfeq; [|discriminate].
      iEval (rewrite /camp_own Hr) in "Hcown". rewrite Ht. iExact "Hcown". }
  iAssert (vlogs_ok γ s' acks vlogs) as "#Hvlogs'".
  { iApply (big_sepM_impl with "Hvlogs_ok"). iIntros "!> %k %x %Hx [%Hxt #Hx]".
    iFrame "Hx". iPureIntro. lia. }
  iAssert (hists_ok γ s' (fp' ++ s'.(pstate.log)) acks) as "#Hhists'".
  { iApply (big_sepM_impl with "Hhists"). iIntros "!> %k %u %Hk #Hk".
    iApply ("Hh" with "[%] Hk"). apply Hacks_term. by eexists. }
  iExists γm, terms, γa, acks, fp', γc, camps, γl, vlogs.
  iFrame "∗#%".
Qed.

Local Lemma own_log_ghost_recs γ id s :
  own_log_ghost γ id s -∗ ⌜ log_ok s ⌝ ∗ log_recs γ s.(pstate.base) s.(pstate.log).
Proof. iIntros "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H". iFrame "#%". Qed.

(** The full log, with what the node keeps of it. *)
Local Lemma own_log_ghost_full γ id s :
  own_log_ghost γ id s -∗
  ∃ fp, ⌜ full_ok s.(pstate.base) fp ∧ plog_wf s.(pstate.base) s.(pstate.log) ∧
          terms_le s (fp ++ s.(pstate.log)) ⌝ ∗
    log_recs γ base0 fp ∗
    commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term) ∗
    camp_own γ id s (fp ++ s.(pstate.log)).
Proof.
  iIntros "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  iExists fp. iSplit; first done. iSplit; first iExact "Hfrecs".
  iSplit; first iExact "Hcommit". iExact "Hcown".
Qed.

Local Lemma own_log_ghost_wf γ id s :
  own_log_ghost γ id s -∗ ⌜ plog_wf s.(pstate.base) s.(pstate.log) ⌝.
Proof.
  iIntros "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  iPureIntro. apply Hfull.
Qed.

Local Lemma own_log_ghost_committed γ id s :
  own_log_ghost γ id s -∗ is_committed γ s.(pstate.commit).
Proof.
  iIntros "H". iDestruct (own_log_ghost_full with "H") as (fp _) "(_ & #Hc & _)".
  iApply (commit_in_committed with "Hc").
Qed.

Local Lemma own_log_ghost_matched γ id s :
  own_log_ghost γ id s -∗ matched_ok γ s.
Proof. iIntros "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H". iFrame "#". Qed.

Local Lemma own_log_ghost_base γ id s :
  own_log_ghost γ id s -∗ base_ok γ s.(pstate.base).
Proof. iIntros "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H". iFrame "#". Qed.

(** The same, for a step that leaves the log alone.  The caller says how
    the commit fact moves to the new commit index. *)
Lemma own_log_ghost_mono' γ id s s' :
  s'.(pstate.log) = s.(pstate.log) →
  s'.(pstate.base) = s.(pstate.base) →
  (s'.(pstate.role) = role.Leader →
     s.(pstate.role) = role.Leader ∧ s'.(pstate.term) = s.(pstate.term)) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  (s'.(pstate.role) = role.Candidate →
     s.(pstate.role) = role.Candidate ∧ s'.(pstate.term) = s.(pstate.term)) →
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  uint.Z s.(pstate.commit) ≤ uint.Z s'.(pstate.commit) →
  bnd s ≤ bnd s' →
  (s'.(pstate.commit) = s.(pstate.commit) ∨
   uint.Z s'.(pstate.commit) ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log)) →
  own_log_ghost γ id s -∗ matched_ok γ s' -∗
  (∀ fp, ⌜ full_ok s.(pstate.base) fp ∧ plog_wf s.(pstate.base) s.(pstate.log) ⌝ -∗
     log_recs γ base0 fp -∗
     commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term) -∗
     commit_in γ (fp ++ s.(pstate.log)) s'.(pstate.commit) s'.(pstate.term)) -∗
  own_log_ghost γ id s'.
Proof.
  iIntros (Hlog Hbase Hlead Hdown Hcand Hle Hcm Hbnd Hcl) "H #Hm' Hcnew".
  iDestruct (own_log_ghost_recs with "H") as "#[%Hok Hr]".
  iDestruct (own_log_ghost_base with "H") as "#Hb".
  iApply (own_log_ghost_upd with "H [] [] Hm' [Hb] [Hcnew]").
  - intros Hr'. destruct (Hlead Hr') as [? ?]. done.
  - done.
  - done.
  - done.
  - done.
  - done.
  - destruct Hok as (? & ? & ?). rewrite /log_ok Hlog Hbase.
    split_and!; [done|lia|]. destruct Hcl as [->|?]; lia.
  - iIntros "!> _ %i _ H". rewrite Hlog Hbase. done.
  - rewrite Hlog Hbase. done.
  - rewrite Hbase. done.
  - iIntros (fp (Hf & Hw & Ht)) "#Hfr #Hc".
    iDestruct ("Hcnew" $! fp with "[%] Hfr Hc") as "#Hc'"; first done.
    iExists fp. iSplit; [|iSplit; [iExact "Hfr"|iSplit]].
    + iPureIntro. rewrite Hlog Hbase. split; [split_and!; [done|done|]|done].
      intros j x Hx. destruct (Ht j x Hx) as [H1 H2]. split; [lia|].
      intros Hc. destruct (Hcand Hc) as [Hc0 ->]. by apply H2.
    + rewrite Hlog. iExact "Hc'".
    + iIntros "!> %t %i _ #H". rewrite Hlog. iApply (hist_mono with "H"). done.
Qed.

(** The same, when [Match] and the commit index do not change either. *)
Lemma own_log_ghost_mono γ id s s' :
  s'.(pstate.log) = s.(pstate.log) →
  s'.(pstate.base) = s.(pstate.base) →
  s'.(pstate.commit) = s.(pstate.commit) →
  (s'.(pstate.role) = role.Leader →
     s.(pstate.role) = role.Leader ∧ s'.(pstate.term) = s.(pstate.term) ∧
     s'.(pstate.matched) = s.(pstate.matched)) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  (s'.(pstate.role) = role.Candidate →
     s.(pstate.role) = role.Candidate ∧ s'.(pstate.term) = s.(pstate.term)) →
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  bnd s ≤ bnd s' →
  own_log_ghost γ id s -∗ own_log_ghost γ id s'.
Proof.
  iIntros (Hlog Hbase Hcm Hlead Hdown Hcand Hle Hbnd) "H".
  iDestruct (own_log_ghost_matched with "H") as "#Hm".
  iApply (own_log_ghost_mono' with "H [] []").
  - done.
  - done.
  - intros Hr'. destruct (Hlead Hr') as (? & ? & ?). done.
  - done.
  - done.
  - done.
  - rewrite Hcm. lia.
  - done.
  - by left.
  - rewrite /matched_ok. destruct (decide (s'.(pstate.role) = role.Leader)) as [Hr'|Hr'].
    + destruct (Hlead Hr') as (Hr & Ht & Hmt).
      iEval (rewrite /matched_ok Hr) in "Hm". rewrite Hr' Ht Hmt. iExact "Hm".
    + destruct (s'.(pstate.role)); [done|done|congruence].
  - iIntros (fp _) "_ #Hc". rewrite Hcm.
    iApply (commit_in_agree with "Hc"); [done|done].
Qed.

(** [bnd] across a step: unfold and compare. *)
Local Ltac bnd_tac :=
  rewrite /bnd /=; repeat case_decide; simpl in *; try lia; exfalso;
  repeat match goal with H : _ ∧ _ |- _ => destruct H end;
  first [ congruence
        | match goal with H : ¬ (_ ∧ _) |- _ => apply H; split; congruence end ].

(** Discharging [own_log_ghost_mono]'s premises for a concrete step. *)
Local Ltac log_mono_tac :=
  simpl; intros; first [ done | congruence | lia | word | (split_and!; done) | bnd_tac ].

(** Adding an acknowledgement to one's own map: fresh, or already there. *)
Local Lemma acks_add γa (acks : gmap (w64 * w64) unit) (k : w64 * w64) :
  ghost_map_auth γa 1 acks -∗ ([∗ map] k ↦ u ∈ acks, k ↪[γa]□ u) ==∗
  ghost_map_auth γa 1 (<[k := ()]> acks) ∗
  ([∗ map] k ↦ u ∈ <[k := ()]> acks, k ↪[γa]□ u) ∗ k ↪[γa]□ ().
Proof.
  iIntros "Hauth #Hfr".
  destruct (acks !! k) as [[]|] eqn:Hk.
  - rewrite insert_id //. iModIntro. iFrame "Hauth Hfr".
    iApply (big_sepM_lookup with "Hfr"). done.
  - iMod (ghost_map_insert_persist k () Hk with "Hauth") as "[Hauth #Hnew]".
    iModIntro. iFrame "Hauth Hnew".
    rewrite big_sepM_insert //. by iFrame "#".
Qed.

Local Lemma acks_term_insert s acks (t i : w64) :
  uint.Z t ≤ uint.Z s.(pstate.term) → acks_term s acks → acks_term s (<[(t, i) := ()]> acks).
Proof.
  intros Ht Hat k [u Hu]. destruct (decide (k = (t, i))) as [->|Hne]; [done|].
  rewrite lookup_insert_ne in Hu; [|done]. apply Hat. by eexists.
Qed.

(** The per-acknowledgement invariants of a new acknowledgement, at the
    node's term: its history, and nothing for the vote-time logs (they are
    of terms up to this one). *)
Local Lemma ack_invs_insert γ s F acks vlogs (i : w64) :
  hist γ F s.(pstate.term) i (bnd s) -∗
  hists_ok γ s F acks -∗ vlogs_ok γ s acks vlogs -∗
  hists_ok γ s F (<[(s.(pstate.term), i) := ()]> acks) ∗
  vlogs_ok γ s (<[(s.(pstate.term), i) := ()]> acks) vlogs.
Proof.
  iIntros "#Hh #Hhs #Hv". iSplit.
  - iApply (big_sepM_insert_2 with "[Hh] Hhs"). done.
  - iApply (big_sepM_impl with "Hv"). iIntros "!> %k %x %Hx [%Hxt #Hx]".
    iSplit; first done. iApply (big_sepM_insert_2 with "[] Hx").
    iIntros (Hlt). simpl in Hlt. lia.
Qed.

(** A node acknowledges at its own term, with the justification
    [acks_ok] asks of it and the history [hists_ok] asks of it. *)
Local Lemma own_log_ghost_ack γ id s i :
  ack_ok γ s (s.(pstate.term), i) -∗
  (∀ fp, ⌜ full_ok s.(pstate.base) fp ∧ plog_wf s.(pstate.base) s.(pstate.log) ⌝ -∗
     log_recs γ base0 fp -∗
     commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term) -∗
     hist γ (fp ++ s.(pstate.log)) s.(pstate.term) i (bnd s)) -∗
  own_log_ghost γ id s ==∗ own_log_ghost γ id s ∗ is_acked γ id s.(pstate.term) i.
Proof.
  iIntros "#Hk Hhnew H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  iDestruct ("Hhnew" $! fp with "[%] Hfrecs Hcommit") as "#Hh"; first (destruct Hfull as (? & ? & ?); done).
  iDestruct (ack_invs_insert with "Hh Hhists Hvlogs_ok") as "[#Hhists' #Hvlogs']".
  iMod (acks_add _ _ (s.(pstate.term), i) with "Hacks Hafrags") as "(Hacks & #Hafr' & #Hnew)".
  assert (Hacks_term' : acks_term s (<[(s.(pstate.term), i) := ()]> acks))
    by (apply (acks_term_insert s); [lia|done]).
  iAssert (acks_ok γ s (<[(s.(pstate.term), i) := ()]> acks)) as "#Hacks_ok'".
  { rewrite /acks_ok. destruct (s.(pstate.role)); [| |done];
      iApply (big_sepM_insert_2 with "[Hk] Hacks_ok"); done. }
  iModIntro. iSplitR "".
  - iExists γm, terms, γa, (<[(s.(pstate.term), i) := ()]> acks), fp, γc, camps, γl, vlogs.
    iFrame "Hcommit Hcown Hhists' Hvlogs' Hacks_ok' Hafr'". iFrame "∗#%".
  - iRight. iExists γa. by iFrame "#%".
Qed.

Local Lemma pleader_entry_term s :
  (pleader_entry s).(raftpb.Entry.Term') = s.(pstate.term).
Proof. done. Qed.

(** A leader's whole log is a log of the leader of its term, with its
    full log and the commit fact about it. *)
Local Lemma own_log_ghost_lead_full γ id s :
  s.(pstate.role) = role.Leader →
  is_leader γ id s.(pstate.term) -∗ own_log_ghost γ id s -∗
  (∃ fp, lead_prefix γ id s.(pstate.term) s.(pstate.base) s.(pstate.log) ∗
     lpfull γ id s.(pstate.term) s.(pstate.base) s.(pstate.log) fp ∗
     commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term)) ∗
  own_log_ghost γ id s.
Proof.
  iIntros (Hr) "#Hl H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  iEval (rewrite /lead_log_own Hr) in "Htlog".
  iDestruct "Htlog" as (γt M l0 Hγt) "(Ha & #Hfr & %Hdom & %Hpre & #Hlf)".
  iPoseProof "Hcown" as "Hcown0". iEval (rewrite /camp_own Hr) in "Hcown0".
  iDestruct "Hcown0" as (F0) "[#Hc0 %HF0]".
  pose proof Hfull as (Hf & Hw & Ht).
  iSplitR "Ha Hterms Hacks Hcamps Hvlogs".
  - iExists fp. iFrame "Hcommit". iSplit.
    + rewrite /lead_prefix. iFrame "Hl". iExists γt, l0. iFrame "#". iSplit.
      * iExists γm. iSplit; first done. iApply (big_sepM_lookup with "Htfrags"). done.
      * iPureIntro. split; [by destruct Hlog_ok|done].
    + iExists F0. iFrame "Hc0 Hfrecs". iPureIntro. split_and!; [done|by destruct HF0 as [? _]|done|].
      intros j x Hx. by destruct (Ht j x Hx).
  - iExists γm, terms, γa, acks, fp, γc, camps, γl, vlogs.
    iFrame "Hcommit Hcown Hhists Hvlogs_ok". iFrame "∗#%".
    rewrite /lead_log_own Hr. iExists γt, M, l0. by iFrame "∗#%".
Qed.

Local Lemma own_log_ghost_lead_prefix γ id s :
  s.(pstate.role) = role.Leader →
  is_leader γ id s.(pstate.term) -∗ own_log_ghost γ id s -∗
  lead_prefix γ id s.(pstate.term) s.(pstate.base) s.(pstate.log) ∗ own_log_ghost γ id s.
Proof.
  iIntros (Hr) "#Hl H".
  iDestruct (own_log_ghost_lead_full with "Hl H") as "[(%fp & $ & _) $]"; done.
Qed.

Lemma bnd_le s : bnd s ≤ uint.Z s.(pstate.term) + 1.
Proof. rewrite /bnd. case_decide; lia. Qed.

Lemma bnd_ge s : uint.Z s.(pstate.term) ≤ bnd s.
Proof. rewrite /bnd. case_decide; lia. Qed.

(** [step_campaign], on the log ghost state: record the campaign log (the
    full log, unchanged since) and, for the self-vote, the vote-time log --
    with the histories of every earlier acknowledgement. *)
Local Lemma own_log_ghost_campaign γ id s :
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.term) + 1 < 2 ^ 64 →
  own_log_ghost γ id s ==∗
  ∃ k F, own_log_ghost γ id (pbecome_candidate id s) ∗
    is_camp γ id (word.add s.(pstate.term) (W64 1)) F ∗
    is_vlog γ id k (word.add s.(pstate.term) (W64 1)) F ∗ log_recs γ base0 F ∗
    ⌜ plog_wf base0 F ∧ plog_last base0 F = plog_last s.(pstate.base) s.(pstate.log) ⌝.
Proof.
  iIntros (Hr Hnw) "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  set (T' := word.add s.(pstate.term) (W64 1)).
  assert (HT' : uint.Z T' = uint.Z s.(pstate.term) + 1) by (rewrite /T'; word).
  destruct Hfull as (Hf & Hw & Htle).
  set (F := fp ++ s.(pstate.log)).
  assert (HwF : plog_wf base0 F) by (by eapply full_wf).
  set (sc := pbecome_candidate id s).
  assert (Hsc_term : sc.(pstate.term) = T') by reflexivity.
  assert (Hsc_role : sc.(pstate.role) = role.Candidate) by reflexivity.
  assert (Hsc_lead : sc.(pstate.lead) = W64 0) by reflexivity.
  assert (Hsc_log : sc.(pstate.log) = s.(pstate.log)) by reflexivity.
  assert (Hsc_base : sc.(pstate.base) = s.(pstate.base)) by reflexivity.
  assert (Hsc_commit : sc.(pstate.commit) = s.(pstate.commit)) by reflexivity.
  clearbody sc.
  assert (Hsc_bnd : bnd sc = uint.Z T').
  { rewrite /bnd Hsc_lead Hsc_role Hsc_term. case_decide as Hc; [done|]. exfalso. apply Hc. done. }
  pose proof (bnd_le s) as Hbs.
  assert (Hcfree : camps !! T' = None).
  { destruct (camps !! T') eqn:Hc; [|done]. exfalso.
    specialize (Hcamps_ok T' ltac:(by eexists)). lia. }
  iMod (ghost_map_insert_persist T' F Hcfree with "Hcamps") as "[Hcamps #Hcf]".
  set (k := fresh (dom vlogs)).
  assert (Hkfree : vlogs !! k = None).
  { apply not_elem_of_dom. apply is_fresh. }
  iMod (ghost_map_insert_persist k (T', F) Hkfree with "Hvlogs") as "[Hvlogs #Hvf]".
  iAssert (is_camp γ id T' F) as "#Hcamp".
  { iExists γc. iFrame "Hcf". iPureIntro. split; [done|]. split; [done|].
    intros j x Hx. destruct (Htle j x Hx) as [? _]. lia. }
  iAssert (log_recs γ base0 F) as "#HrF".
  { iApply (log_recs_full with "Hfrecs Hrecs"). done. }
  iModIntro. iExists k, F.
  iSplitR "".
  2:{ iFrame "Hcamp HrF". iSplit; [iExists γl; by iFrame "#%"|].
      iPureIntro. split; [done|]. by apply full_last. }
  assert (Hterms_ok' : terms_ok terms sc).
  { intros t Ht. left. rewrite Hsc_term HT'.
    destruct (Hterms_ok t Ht) as [? | [_ ?]]; [lia|done]. }
  assert (Hacks_term' : acks_term sc acks).
  { intros kk Hk. specialize (Hacks_term kk Hk). rewrite Hsc_term HT'. lia. }
  assert (Hlog_ok' : log_ok sc) by (rewrite /log_ok Hsc_base Hsc_log Hsc_commit; exact Hlog_ok).
  assert (Hfull' : full_ok sc.(pstate.base) fp ∧ plog_wf sc.(pstate.base) sc.(pstate.log) ∧
                   terms_le sc (fp ++ sc.(pstate.log))).
  { rewrite Hsc_base Hsc_log. split_and!; [done|done|]. intros j x Hx. rewrite Hsc_term HT'.
    destruct (Htle j x Hx) as [? _]. split; intros; lia. }
  assert (Hcamps_ok' : ∀ T, is_Some (<[T' := F]> camps !! T) → uint.Z T ≤ uint.Z sc.(pstate.term)).
  { intros T [x Hx]. rewrite Hsc_term HT'. destruct (decide (T = T')) as [->|Hne]; [lia|].
    rewrite lookup_insert_ne // in Hx. specialize (Hcamps_ok T ltac:(by eexists)). lia. }
  iAssert (lead_log_own γ sc terms) as "Htlog'".
  { rewrite /lead_log_own Hsc_role //. }
  iAssert (acks_ok γ sc acks) as "#Hacks_ok'".
  { rewrite /acks_ok Hsc_role. iApply big_sepM_intro. iIntros "!> %kk %u %Hk".
    iIntros ([Hk1 _]). exfalso. specialize (Hacks_term kk ltac:(by eexists)).
    rewrite Hk1 Hsc_term HT' in Hacks_term. lia. }
  iAssert (matched_ok γ sc) as "#Hmatched'".
  { rewrite /matched_ok Hsc_role. done. }
  iAssert (commit_in γ (fp ++ sc.(pstate.log)) sc.(pstate.commit) sc.(pstate.term)) as "#Hcommit'".
  { rewrite Hsc_log Hsc_commit. iApply (commit_in_agree with "Hcommit"); [|done]. rewrite Hsc_term HT'. lia. }
  iAssert (camp_own γ id sc (fp ++ sc.(pstate.log))) as "#Hcown'".
  { rewrite /camp_own Hsc_role Hsc_term Hsc_log. iExact "Hcamp". }
  iAssert (log_recs γ sc.(pstate.base) sc.(pstate.log)) as "#Hrecs'".
  { rewrite Hsc_base Hsc_log. iExact "Hrecs". }
  iAssert (base_ok γ sc.(pstate.base)) as "#Hbase'".
  { rewrite Hsc_base. iExact "Hbase". }
  iAssert (vlogs_ok γ sc acks (<[k := (T', F)]> vlogs)) as "#Hvlogs'".
  { iApply big_sepM_insert_2.
    - iSplit; first (iPureIntro; simpl; rewrite Hsc_term; lia).
      iApply (big_sepM_impl with "Hhists"). iIntros "!> %kk %u %Hk #Hh %Hlt".
      iApply (hist_mono with "Hh"). simpl. lia.
    - iApply (big_sepM_impl with "Hvlogs_ok"). iIntros "!> %kk %x %Hx [%Hxt #Hx]".
      iFrame "Hx". iPureIntro. rewrite Hsc_term. lia. }
  iAssert (hists_ok γ sc (fp ++ sc.(pstate.log)) acks) as "#Hhists'".
  { rewrite Hsc_log. iApply (big_sepM_impl with "Hhists"). iIntros "!> %kk %u %Hk #Hh".
    iApply (hist_mono with "Hh"). rewrite Hsc_bnd. lia. }
  iExists γm, terms, γa, acks, fp, γc, (<[T' := F]> camps), γl, (<[k := (T', F)]> vlogs).
  iFrame "Hcommit' Hcown' Hhists' Hvlogs' Hacks_ok' Hmatched' Hrecs' Hbase'".
  iFrame "Hterms Hacks Hcamps Hvlogs Htlog' Htfrags Hafrags Hfrecs".
  iPureIntro. done.
Qed.

(** A first vote, on the log ghost state: record the vote-time log, which
    has the histories of all acknowledgements (the bound is the term: a
    first vote is cast with no leader). *)
Local Lemma own_log_ghost_vote γ id s :
  bnd s = uint.Z s.(pstate.term) →
  own_log_ghost γ id s ==∗
  ∃ k F, own_log_ghost γ id s ∗ is_vlog γ id k s.(pstate.term) F ∗ log_recs γ base0 F ∗
    ⌜ plog_wf base0 F ∧
      ∀ x, plog_up_to_date base0 F x = plog_up_to_date s.(pstate.base) s.(pstate.log) x ⌝.
Proof.
  iIntros (Hbnd) "H". iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  pose proof Hfull as (Hf & Hw & Htle).
  set (F := fp ++ s.(pstate.log)).
  set (k := fresh (dom vlogs)).
  assert (Hkfree : vlogs !! k = None).
  { apply not_elem_of_dom. apply is_fresh. }
  iMod (ghost_map_insert_persist k (s.(pstate.term), F) Hkfree with "Hvlogs") as "[Hvlogs #Hvf]".
  iAssert (vlogs_ok γ s acks (<[k := (s.(pstate.term), F)]> vlogs)) as "#Hvlogs'".
  { iApply big_sepM_insert_2; [|iExact "Hvlogs_ok"].
    iSplit; first (iPureIntro; simpl; lia).
    iApply (big_sepM_impl with "Hhists"). iIntros "!> %kk %u %Hk #Hh %Hlt".
    simpl. rewrite -Hbnd. iExact "Hh". }
  iModIntro. iExists k, F.
  iSplitR "".
  2:{ iSplit; [iExists γl; by iFrame "#%"|]. iSplit.
      - iApply (log_recs_full with "Hfrecs Hrecs"). done.
      - iPureIntro. split; [by eapply full_wf|]. intros x. by apply full_up_to_date. }
  iExists γm, terms, γa, acks, fp, γc, camps, γl, (<[k := (s.(pstate.term), F)]> vlogs).
  iFrame "Hcommit Hcown Hhists Hvlogs' Hacks_ok Hmatched".
  iFrame "Hterms Hacks Hcamps Hvlogs Htlog Htfrags Hafrags Hrecs Hbase Hfrecs".
  iPureIntro. done.
Qed.


(** What a leader's [MsgSnap] carries beyond its leadership.  [Qed] since
    2026-10-03 (admitted from 2026-10-02 as a client assumption, before
    [snap_ok] carried the commit bound and the log fact): [is_committed] is
    [is_committed_le] of the commit index; [is_snap_meta] is the log's
    record of the entry at [m.index] ([log_recs]), or, when the snapshot
    is exactly at the base, [own_log_ghost]'s [base_ok]. *)
Local Lemma snap_ok_message γ id s m :
  plog_wf_r s.(pstate.base) s.(pstate.log) →
  snap_ok id s m →
  is_committed γ s.(pstate.commit) -∗
  log_recs γ s.(pstate.base) s.(pstate.log) -∗
  base_ok γ s.(pstate.base) -∗
  is_committed γ m.(msg.index) ∗ is_snap_meta γ m.(msg.logterm) m.(msg.index) ∗
  ⌜ plog_term_at s.(pstate.base) s.(pstate.log) m.(msg.index) = Some m.(msg.logterm) ⌝.
Proof.
  iIntros (Hwf Hsnap) "#Hc #Hrecs #Hb".
  destruct Hsnap as (_ & _ & _ & _ & Hnz & Hle & Hidx).
  iSplit; first (iApply (is_committed_le with "Hc"); lia).
  iSplit; last done.
  pose proof (plog_term_at_Some_range _ _ _ _ Hidx) as [Hlo Hhi].
  pose proof (word.unsigned_range m.(msg.index)) as Hmr.
  destruct (decide (uint.Z m.(msg.index) = uint.Z s.(pstate.base).(raft.entryID.index')))
    as [Heq|Hne].
  - (* at the base: [base_ok] *)
    assert (Hi : m.(msg.index) = s.(pstate.base).(raft.entryID.index')) by word.
    rewrite Hi plog_term_at_base in Hidx. injection Hidx as Ht.
    iDestruct "Hb" as "[%H0 | Hm]".
    + exfalso. apply Hnz. rewrite Hi. word.
    + rewrite Hi -Ht. iExact "Hm".
  - (* above it: the record of the entry at [m.index] *)
    set (k := Z.to_nat (uint.Z m.(msg.index) - uint.Z s.(pstate.base).(raft.entryID.index') - 1)).
    assert (Hk : ∃ e, s.(pstate.log) !! k = Some e ∧ e.(raftpb.Entry.Term') = m.(msg.logterm)).
    { rewrite /plog_term_at decide_False in Hidx; [|lia]. rewrite decide_False in Hidx; [|done].
      fold k in Hidx.
      destruct (s.(pstate.log) !! k) as [e|] eqn:He; [|done].
      injection Hidx as Ht. by exists e. }
    destruct Hk as (e & Hk & Ht).
    assert (Hr : uint.Z s.(pstate.base).(raft.entryID.index') + Z.of_nat k + 1 < 2 ^ 64)
      by (unfold k; lia).
    iDestruct (big_sepL_lookup with "Hrecs") as "He"; first exact Hk.
    rewrite decide_True //. iDestruct "He" as (pt _) "He".
    iExists e. iSplit; first (iExists pt; iExact "He").
    iPureIntro. split; [done|].
    apply word.unsigned_inj. rewrite (Hwf k e Hk Hr). unfold k. lia.
Qed.

(** What a leader's broadcast carries, from what the leader holds. *)
Local Lemma repl_ok_message γ id s m fp :
  plog_wf_r s.(pstate.base) s.(pstate.log) →
  repl_ok id s m → id ≠ W64 0 →
  is_leader γ id s.(pstate.term) -∗
  lead_prefix γ id s.(pstate.term) s.(pstate.base) s.(pstate.log) -∗
  lpfull γ id s.(pstate.term) s.(pstate.base) s.(pstate.log) fp -∗
  log_recs γ s.(pstate.base) s.(pstate.log) -∗
  commit_in γ (fp ++ s.(pstate.log)) s.(pstate.commit) s.(pstate.term) -∗
  base_ok γ s.(pstate.base) -∗
  is_message γ m.
Proof.
  iIntros (Hr Hok Hid) "#Hl #Hp #Hlf #Hrecs #Hc #Hb".
  iPoseProof "Hlf" as (F0) "(_ & #Hfr & %Hfull & _ & %Hwl & _)".
  iDestruct (log_recs_full with "Hfr Hrecs") as "#HrF"; first done.
  pose proof (full_wf _ _ _ Hfull Hwl) as HwF.
  destruct Hok as [(Hty & Hfrom & Hterm & _ & Hidx & Hcm & _ & Hpre & Hpay) | Hsnap].
  - rewrite /is_message Hty Hfrom Hterm.
    iSplit; first (iPureIntro; exact Hpay). iSplit; first iExact "Hl".
    iSplit; last done.
    iExists s.(pstate.base), s.(pstate.log), fp. iSplit; first iExact "Hp".
    iSplit; first (iPureIntro; split; done). iSplit; first iExact "Hlf".
    iApply (commit_in_le with "HrF Hc"); done.
  - iDestruct (commit_in_committed with "Hc") as "#Hc'".
    iDestruct (snap_ok_message γ id s m Hr Hsnap with "Hc' Hrecs Hb") as "(_ & Hmeta & %Hidx)".
    pose proof Hsnap as (Hty & Hfrom & Hterm & _ & _ & Hle & _).
    rewrite /is_message Hty Hfrom Hterm.
    iSplit; first iExact "Hl". iSplit; first iExact "Hmeta". iSplit; last done.
    iExists s.(pstate.base), s.(pstate.log), fp. iSplit; first iExact "Hp".
    iSplit; first done. iSplit; first iExact "Hlf".
    iApply (commit_in_le with "HrF Hc"); done.
Qed.

(** A full log at its commit index has the history of an
    acknowledgement there, at any term at least the commit fact's. *)
Local Lemma hist_of_commit γ F (c tm : w64) B :
  plog_wf base0 F → uint.Z tm < B →
  log_recs γ base0 F -∗ commit_in γ F c tm -∗ hist γ F tm c B.
Proof.
  iIntros (HwF HB) "#HrF [%H0 | (%t & %n & %G & #Hq & %Hc & %Ht & %HG)]".
  { iIntros (j Hj). lia. }
  iPoseProof "Hq" as "(%Hn & #Hfl & _)".
  assert (HsG : is_Some (plog_term_at base0 G c)).
  { apply (full_term_at_some _ _ n); [by eexists|lia]. }
  iApply (hist_of_agree _ F G with "HrF"); [done|done|done|].
  destruct (decide (t = tm)) as [->|Hne].
  - iLeft. iExists tm. iFrame "Hfl". iPureIntro. lia.
  - iRight. iExists t, n. iFrame "Hq". iPureIntro. split; [|lia].
    assert (uint.Z t ≠ uint.Z tm) by (intros ?; apply Hne; by apply word.unsigned_inj). lia.
Qed.

(** An acknowledgement justified by the log, in full-log terms. *)
Local Lemma ack_agree_full γ b es fp (t i : w64) :
  full_ok b fp → uint.Z b.(raft.entryID.index') ≤ uint.Z i →
  ack_agree γ b es t i -∗
  ∃ X, lead_full γ t X ∗
    ⌜ is_Some (plog_term_at base0 X i) ∧
      plog_term_at base0 X i = plog_term_at base0 (fp ++ es) i ⌝.
Proof.
  iIntros (Hf Hb) "(_ & %ldr & %bL & %l & #Hp & [%Hs %Heq] & %fpX & #Hpf)".
  iExists (fpX ++ l). iSplit; first iApply (lead_full_intro with "Hp Hpf").
  iPoseProof "Hpf" as (F0) "(_ & _ & %HfX & _)".
  destruct Hs as [x Hx]. pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [HbL _].
  rewrite (full_term_at bL fpX l) // (full_term_at b fp es) //.
Qed.

(** A non-leader's own acknowledgement of its term above its commit index
    is justified by its log. *)
Local Lemma own_log_ghost_ack_agree γ id s (i : w64) :
  own_log_ghost γ id s -∗ is_acked γ id s.(pstate.term) i -∗
  ∀ _ : s.(pstate.role) ≠ role.Leader ∧ uint.Z s.(pstate.commit) < uint.Z i,
    ack_agree γ s.(pstate.base) s.(pstate.log) s.(pstate.term) i.
Proof.
  iIntros "H [%H0 | (%γa' & %Hγa' & #Hfrag)]"; [iIntros ([_ Hlt]); word|].
  iDestruct "H" as (γm terms γa acks fp γc camps γl vlogs) "H". iNamed "H".
  rewrite Haname in Hγa'. injection Hγa' as <-.
  iDestruct (ghost_map_lookup with "Hacks Hfrag") as %Hk.
  iIntros ([Hr Hlt]).
  rewrite /acks_ok. destruct (s.(pstate.role)); [| |congruence].
  all: iDestruct (big_sepM_lookup with "Hacks_ok") as "Hk"; first exact Hk.
  all: iApply ("Hk" $! (conj eq_refl Hlt)).
Qed.

(** Histories across a log change that keeps the log below [c], puts a
    leader's log [Y] (of a term in range) on [[c, L]], and drops what is
    past [L] -- where the old log disagreed with [Y] at some [k] in
    [[c, L]] (the cut of [step_app_accept], the snapshot index of
    [step_snap_restore]). *)
Local Lemma hist_replace γ F F' Y (t i T : w64) B B' (c : Z) (k L : w64) :
  B ≤ B' → uint.Z t ≤ uint.Z T → uint.Z T < B' →
  0 < uint.Z k → c ≤ uint.Z k ≤ uint.Z L →
  (∀ j : w64, uint.Z j < c → plog_term_at base0 F' j = plog_term_at base0 F j) →
  (∀ j : w64, c ≤ uint.Z j ≤ uint.Z L →
     plog_term_at base0 F' j = plog_term_at base0 Y j ∧ is_Some (plog_term_at base0 Y j)) →
  plog_term_at base0 F k ≠ plog_term_at base0 Y k →
  (∀ j : w64, uint.Z L < uint.Z j → plog_term_at base0 F' j = None) →
  lead_full γ T Y -∗ hist γ F t i B -∗ hist γ F' t i B'.
Proof.
  iIntros (HB Ht HT Hk0 Hk Hlow Hmid Hdiff Hhigh) "#HY #Hh %j %Hj".
  iAssert (∀ j', okL γ t B' j' Y)%I as "#HokY".
  { iIntros (j'). iLeft. iExists T. iFrame "HY". iPureIntro. lia. }
  destruct (decide (uint.Z j < c)) as [Hjc|Hjc].
  - iDestruct ("Hh" $! j Hj) as "[(%X & #HX & %Hs & %HXj) | (%j' & %X1 & %X2 & %Hj' & #H1 & #H2 & %Hd)]".
    + iLeft. iExists X. iSplit; first (iApply (okL_mono with "HX"); done).
      iPureIntro. rewrite Hlow //.
    + iRight. iExists j', X1, X2. iSplit; first done.
      iSplit; first (iApply (okL_mono with "H1"); done).
      iSplit; first (iApply (okL_mono with "H2"); done). done.
  - destruct (decide (uint.Z j ≤ uint.Z L)) as [HjL|HjL].
    + destruct (Hmid j ltac:(lia)) as [Heq Hs].
      iLeft. iExists Y. iSplit; first iApply "HokY". iPureIntro. by rewrite Heq.
    + iRight.
      destruct (Hmid k ltac:(lia)) as [_ HsY].
      assert (Hkj : 0 < uint.Z k ≤ uint.Z i) by lia.
      iDestruct ("Hh" $! k Hkj) as "[(%X & #HX & %Hs & %HXk) | (%j' & %X1 & %X2 & %Hj' & #H1 & #H2 & %Hd)]".
      * iExists k, X, Y. iSplit; first (iPureIntro; lia).
        iSplit; first (iApply (okL_mono with "HX"); done).
        iSplit; first iApply "HokY".
        iPureIntro. split_and!; [done|done|]. rewrite HXk. done.
      * iExists j', X1, X2. iSplit; first (iPureIntro; lia).
        iSplit; first (iApply (okL_mono with "H1"); done).
        iSplit; first (iApply (okL_mono with "H2"); done). done.
Qed.

(** *** The refinement obligation, one rule at a time

    The election rules are proved inline in [own_raft_ghost_step]; the
    replication rules each have a lemma here. *)

Local Ltac destruct_ghost :=
  iDestruct "Hown" as (γv voted)
    "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead & Hlg & %Hlok & %Hfv & #Hvrecs & %Hrok)".

(** [role_ok] of the state a rule produces: unchanged role, vote and
    leader, or a follower. *)
Local Ltac role_ok_tac :=
  first
    [ assumption
    | let H1 := fresh in let H2 := fresh in
      match goal with H : role_ok _ _ |- _ => pose proof H as [H1 H2] end;
      rewrite /role_ok /psend_msgs /padopt_leader /pbecome_follower /=; split; intros ?;
      first [ congruence | done | by apply H1 | by apply H2 ] ].

(** [lead_ok] of the state a rule produces: unchanged role and leader, or a
    leader, or a follower with no leader / another node as leader. *)
Local Ltac lead_ok_tac :=
  first
    [ assumption
    | rewrite /lead_ok /=; intros Hr;
      first [ by exfalso; apply Hr | assumption | congruence ] ].

(** [follower_votes_ok] of the state a rule produces, likewise. *)
Local Ltac follower_votes_tac :=
  first
    [ assumption
    | rewrite /follower_votes_ok /=; intros Hr; first [ done | congruence ] ].

(** [step_win]: allocate the term log -- recording the candidate's base and
    log, and holding the leader's entry -- and acknowledge the old and the
    new last index. *)
Local Lemma own_raft_ghost_step_win γ id s mt ms :
  s.(pstate.role) = role.Candidate →
  is_quorum γ.(re_cfg) (granted s.(pstate.votes)) →
  plog_last_index_Z s.(pstate.base) s.(pstate.log) + 1 < 2 ^ 64 →
  leader_match_ok id s mt →
  Forall (repl_ok id (pwin_state id s mt)) ms →
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id (psend_msgs (pwin_state id s mt)
                         ([pself_ack id (pwin_state id s mt)] ++ ms)).
Proof.
  intros Hrole Hq Hnw [Hmid Hmoth] Hms.
  (* name the new state and record what it is, then forget its body, so
     that no [simpl] below unfolds it on one side of a match only *)
  set (s2 := pwin_state id s mt) in *.
  assert (Hs2log : s2.(pstate.log) = s.(pstate.log) ++ [pleader_entry s]) by reflexivity.
  assert (Hs2out : s2.(pstate.outbox) = s.(pstate.outbox)) by reflexivity.
  assert (Hs2term : s2.(pstate.term) = s.(pstate.term)) by reflexivity.
  assert (Hs2vote : s2.(pstate.vote) = s.(pstate.vote)) by reflexivity.
  assert (Hs2votes : s2.(pstate.votes) = ∅) by reflexivity.
  assert (Hs2role : s2.(pstate.role) = role.Leader) by reflexivity.
  assert (Hs2commit : s2.(pstate.commit) = s.(pstate.commit)) by reflexivity.
  assert (Hs2base : s2.(pstate.base) = s.(pstate.base)) by reflexivity.
  assert (Hs2matched : s2.(pstate.matched) = mt) by reflexivity.
  assert (Hs2lead : s2.(pstate.lead) = id) by reflexivity.
  clearbody s2.
  set (sf := psend_msgs s2 ([pself_ack id s2] ++ ms)).
  assert (Hsflog : sf.(pstate.log) = s2.(pstate.log)) by reflexivity.
  assert (Hsfterm : sf.(pstate.term) = s.(pstate.term)) by (rewrite -Hs2term; reflexivity).
  assert (Hsfrole : sf.(pstate.role) = role.Leader) by (rewrite -Hs2role; reflexivity).
  assert (Hsfcommit : sf.(pstate.commit) = s.(pstate.commit)) by (rewrite -Hs2commit; reflexivity).
  assert (Hsfbase : sf.(pstate.base) = s.(pstate.base)) by (rewrite -Hs2base; reflexivity).
  assert (Hsfmatched : sf.(pstate.matched) = mt) by (rewrite -Hs2matched; reflexivity).
  assert (Hsfbnd : bnd sf = uint.Z s.(pstate.term) + 1).
  { rewrite /bnd Hsfterm Hsfrole decide_False //. intros [_ Hr]. by apply Hr. }
  iIntros "Hown". destruct_ghost.
  assert (Hsbnd : bnd s = uint.Z s.(pstate.term)).
  { rewrite /bnd decide_True //. split; [apply Hrok; done|congruence]. }
  iAssert (is_leader γ id s.(pstate.term)) as "#Hnewlead".
  { iExists (granted s.(pstate.votes)). by iFrame "#". }
  iDestruct "Hlg" as (γm terms γa acks fp γc camps γl vlogs) "Hlg". iNamed "Hlg".
  destruct Hlog_ok as (Hwf & Hbc & Hcl).
  destruct Hfull as (Hfp & Hwl & Htle).
  iEval (rewrite /camp_own Hrole) in "Hcown".
  set (F := fp ++ s.(pstate.log)).
  assert (HwF : plog_wf base0 F) by (by eapply full_wf).
  (* the current term has no term log: the node was not leader in it *)
  assert (Hfree : terms !! s.(pstate.term) = None).
  { destruct (terms !! s.(pstate.term)) eqn:Ht; last done.
    exfalso. destruct (Hterms_ok s.(pstate.term) ltac:(by eexists)) as [Hlt | [_ Hr]].
    - lia.
    - congruence. }
  set (e := pleader_entry s).
  set (pt0 := (plog_last s.(pstate.base) s.(pstate.log)).(raft.entryID.term')).
  set (L := plog_last_index_Z s.(pstate.base) s.(pstate.log)).
  pose proof (plog_last_index_Z_nonneg s.(pstate.base) s.(pstate.log)) as HL0.
  assert (HLF : plog_last_index_Z base0 F = L) by (by apply full_last_index).
  assert (HlastF : plog_last base0 F = plog_last s.(pstate.base) s.(pstate.log))
    by (by apply full_last).
  (* the leader's entry, at [L + 1] *)
  assert (Heidx : uint.Z e.(raftpb.Entry.Index') = L + 1).
  { pose proof (stamp_index_eq L 0 HL0 ltac:(lia)) as H.
    rewrite /e /pleader_entry /stamp /plast_index /=. rewrite /L in H. simpl in H. lia. }
  assert (Heterm : e.(raftpb.Entry.Term') = s.(pstate.term)) by done.
  (* the candidate's last term is below its term *)
  assert (Hpt0 : uint.Z pt0 < uint.Z s.(pstate.term)).
  { pose proof (plog_term_at_last base0 F HwF) as Hlt.
    rewrite HlastF in Hlt. by apply (Htle _ _ Hlt). }
  iMod (ghost_map_alloc {[ e.(raftpb.Entry.Index') := (e, pt0) ]}) as (γt) "[Htauth Htel]".
  rewrite big_sepM_singleton.
  iMod (ghost_map_elem_persist with "Htel") as "#Htel".
  iMod (ghost_map_insert_persist s.(pstate.term) (γt, s.(pstate.base), s.(pstate.log)) Hfree
         with "Hterms") as "[Hterms #Htnew]".
  iAssert (is_term_log γ id s.(pstate.term) γt s2.(pstate.base) s.(pstate.log)) as "#Htl".
  { iExists γm. rewrite Hs2base. by iFrame "#%". }
  iAssert (is_entry_r γ e pt0) as "#He".
  { iExists id, γt, s2.(pstate.base), s.(pstate.log), F. rewrite /e pleader_entry_term.
    iFrame "#". iPureIntro. rewrite /pt_ok -/e HLF Heidx HlastF.
    split_and!; [lia|lia|done|lia]. }
  assert (Hwl2 : plog_wf s2.(pstate.base) s2.(pstate.log)).
  { rewrite Hs2log Hs2base. apply plog_wf_app. split; [done|].
    intros k x Hk. apply list_lookup_singleton_Some in Hk as [-> <-].
    rewrite Heidx /L /plog_last_index_Z. lia. }
  assert (Hwf2 : plog_wf_r s2.(pstate.base) s2.(pstate.log)) by (by apply plog_wf_wf_r).
  set (F2 := fp ++ s2.(pstate.log)).
  assert (HF2 : F2 = F ++ [e]) by (rewrite /F2 /F Hs2log app_assoc //).
  assert (HwF2 : plog_wf base0 F2).
  { rewrite /F2. apply (full_wf s.(pstate.base)); [exact Hfp|rewrite -Hs2base; exact Hwl2]. }
  assert (HLF2 : plog_last_index_Z base0 F2 = L + 1).
  { rewrite HF2 /plog_last_index_Z length_app /= base0_index.
    rewrite /plog_last_index_Z base0_index in HLF. lia. }
  (* [F2] keeps [F]'s terms, and has [T] at [L + 1] *)
  assert (HkeepF : ∀ j : w64, is_Some (plog_term_at base0 F j) →
                     plog_term_at base0 F2 j = plog_term_at base0 F j).
  { intros j [x Hx]. rewrite HF2. apply plog_term_at_app_l.
    by pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ ?]. }
  assert (HtF2 : ∀ (j x : w64), plog_term_at base0 F2 j = Some x →
                   uint.Z x ≤ uint.Z s.(pstate.term)).
  { intros j x Hx. pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ Hj].
    destruct (decide (uint.Z j ≤ L)) as [Hle|Hgt].
    - rewrite HF2 plog_term_at_app_l in Hx; [|lia].
      destruct (Htle _ _ Hx) as [? _]. lia.
    - rewrite HF2 plog_term_at_app_r in Hx; [|lia].
      replace (Z.to_nat _) with 0%nat in Hx by lia. simpl in Hx.
      injection Hx as <-. lia. }
  iAssert (log_recs γ s2.(pstate.base) s2.(pstate.log)) as "#Hrecs2".
  { rewrite /log_recs Hs2log Hs2base big_sepL_app big_sepL_singleton. iSplit.
    - iApply (big_sepL_impl with "Hrecs"). iIntros "!> %k %x %Hk H".
      case_decide as Hr; [|done]. iDestruct "H" as (pt Hpt) "Hx". iExists pt. iFrame "Hx".
      iPureIntro. rewrite plog_term_at_app_l; [done|].
      apply lookup_lt_Some in Hk. rewrite /pidx word.unsigned_of_Z_nowrap.
      + rewrite /plog_last_index_Z. lia.
      + pose proof (word.unsigned_range s.(pstate.base).(raft.entryID.index')). lia.
    - case_decide as Hr; [|done]. iExists pt0. iFrame "He". iPureIntro.
      rewrite Nat.add_0_r.
      assert (Hp : pidx s.(pstate.base) (length s.(pstate.log)) = W64 L) by done.
      rewrite Hp plog_term_at_app_l; last first.
      { rewrite word.unsigned_of_Z_nowrap; [rewrite /L; lia|]. split; [lia|].
        rewrite /L /plog_last_index_Z. lia. }
      apply plog_term_at_last_r; [done|]. rewrite /plog_last_index_Z. lia. }
  iDestruct (log_recs_full with "Hfrecs Hrecs2") as "#HrF2"; first (rewrite Hs2base //).
  iAssert (lead_frags γt s.(pstate.log) s2.(pstate.log)) as "#Hlf2".
  { rewrite /lead_frags Hs2log big_sepL_app big_sepL_singleton. iSplit.
    - iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      apply lookup_lt_Some in Hk. rewrite decide_False //. lia.
    - rewrite decide_True; [|lia]. iExists pt0. iFrame "Htel". }
  iAssert (lead_prefix γ id s2.(pstate.term) s2.(pstate.base) s2.(pstate.log)) as "#Hp2".
  { rewrite /lead_prefix Hs2term. iFrame "Hnewlead". iExists γt, s.(pstate.log). iFrame "Htl Hrecs2 Hlf2".
    iPureIntro. split; [done|]. rewrite Hs2log. by apply prefix_app_r. }
  iAssert (lpfull γ id s2.(pstate.term) s2.(pstate.base) s2.(pstate.log) fp) as "#Hpf2".
  { iExists F. rewrite Hs2term Hs2base. iFrame "Hcown Hfrecs". iPureIntro.
    split_and!; [done| |rewrite -Hs2base //|exact HtF2].
    rewrite -/F2 HF2. by apply prefix_app_r. }
  iDestruct (lead_full_intro with "Hp2 Hpf2") as "#Hfull2".
  iAssert (is_leader γ id s2.(pstate.term)) as "#Hnewlead2".
  { rewrite Hs2term. iFrame "#". }
  iAssert (commit_in γ F2 s2.(pstate.commit) s2.(pstate.term)) as "#Hcommit2".
  { rewrite Hs2commit Hs2term. iApply (commit_in_agree with "Hcommit"); [done|].
    apply HkeepF. apply plog_term_at_in_range. rewrite base0_index HLF. word. }
  iAssert (base_ok γ s2.(pstate.base)) as "#Hbase2".
  { rewrite Hs2base. iExact "Hbase". }
  (* the two acknowledgements, with their histories *)
  iAssert (∀ i : w64, ⌜ uint.Z i ≤ L + 1 ⌝ -∗ hist γ F2 s.(pstate.term) i (bnd sf))%I as "#Hhnew".
  { iIntros (i Hi). iApply (hist_of_agree _ F2 F2 with "HrF2 []"); [done| |done|].
    - apply plog_term_at_in_range. rewrite base0_index HLF2. word.
    - iLeft. iExists s.(pstate.term). rewrite Hsfbnd -Hs2term -/F2. iFrame "Hfull2". iPureIntro. lia. }
  iAssert (hists_ok γ sf F2 acks) as "#Hhists2".
  { iApply (big_sepM_impl with "Hhists"). iIntros "!> %k %u %Hk #Hk".
    iApply (hist_mono γ F2 k.1 k.2 (bnd s) (bnd sf) with "[Hk]"); [rewrite Hsfbnd Hsbnd; lia|].
    iApply (hist_keep with "Hk"). intros j _ Hj. by apply HkeepF. }
  iAssert (vlogs_ok γ sf acks vlogs) as "#Hvlogs2".
  { iApply (big_sepM_impl with "Hvlogs_ok"). iIntros "!> %k %x %Hx [%Hxt #Hx]".
    iFrame "Hx". iPureIntro. rewrite Hsfterm. lia. }
  iDestruct (ack_invs_insert _ sf F2 _ _ (plast_index s) with "[] Hhists2 Hvlogs2")
    as "[#Hhists3 #Hvlogs3]".
  { rewrite Hsfterm. iApply "Hhnew". iPureIntro. rewrite /plast_index -/L. word. }
  iDestruct (ack_invs_insert _ sf F2 _ _ (plast_index s2) with "[] Hhists3 Hvlogs3")
    as "[#Hhists4 #Hvlogs4]".
  { rewrite Hsfterm. iApply "Hhnew". iPureIntro.
    rewrite /plast_index Hs2log Hs2base /plog_last_index_Z length_app /=.
    rewrite /L /plog_last_index_Z in Hnw |- *. word. }
  rewrite Hsfterm.
  iMod (acks_add _ _ (s.(pstate.term), plast_index s) with "Hacks Hafrags")
    as "(Hacks & #Hafr1 & #Hk1)".
  iMod (acks_add _ _ (s.(pstate.term), plast_index s2) with "Hacks Hafr1")
    as "(Hacks & #Hafr2 & #Hk2)".
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [-] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | idtac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); [exact Hs2term|exact Hs2vote].
  - rewrite psend_msgs_outbox Hs2out big_sepL_app.
    iSplitR; [iFrame "#"|]. rewrite big_sepL_cons. iSplitR.
    + rewrite /is_message /pself_ack /=. iRight. iExists γa. rewrite -Hs2term. by iFrame "#%".
    + iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      iApply (repl_ok_message _ id s2 _ fp with "Hnewlead2 Hp2 Hpf2 Hrecs2 Hcommit2 Hbase2").
      * done.
      * exact (Forall_lookup_1 _ _ _ _ Hms Hk).
      * done.
  - rewrite psend_msgs_votes Hs2votes granted_empty big_sepS_empty //.
  - rewrite /leader_wit psend_msgs_role Hs2role psend_msgs_term. iFrame "#".
  - assert (Hterms_ok' : terms_ok (<[s.(pstate.term) := (γt, s.(pstate.base), s.(pstate.log))]> terms) sf).
    { intros t Ht. rewrite Hsfterm Hsfrole.
      destruct (decide (t = s.(pstate.term))) as [->|Hne]; first by right.
      rewrite lookup_insert_ne // in Ht.
      destruct (Hterms_ok t Ht) as [Hlt | [-> Hr]]; [by left | congruence]. }
    assert (Hacks_term' : acks_term sf (<[(s.(pstate.term), plast_index s2) := ()]>
                                        (<[(s.(pstate.term), plast_index s) := ()]> acks))).
    { rewrite /acks_term Hsfterm.
      apply (acks_term_insert s); [lia|]. apply (acks_term_insert s); [lia|done]. }
    assert (Hlog_ok' : log_ok sf).
    { rewrite /log_ok Hsfbase Hsflog Hsfcommit.
      split_and!; [rewrite -Hs2base; done|done|].
      rewrite Hs2log /plog_last_index_Z length_app /=.
      rewrite /plog_last_index_Z in Hcl. lia. }
    assert (Hfull' : full_ok sf.(pstate.base) fp ∧ plog_wf sf.(pstate.base) sf.(pstate.log) ∧
                     terms_le sf (fp ++ sf.(pstate.log))).
    { rewrite Hsfbase Hsflog. split_and!; [done|rewrite -Hs2base //|].
      intros j x Hx. rewrite Hsfterm Hsfrole. split; [by apply (HtF2 j x)|done]. }
    assert (Hcamps_ok' : ∀ T, is_Some (camps !! T) → uint.Z T ≤ uint.Z sf.(pstate.term)).
    { intros T HT. rewrite Hsfterm. by apply Hcamps_ok. }
    iAssert (camp_own γ id sf (fp ++ sf.(pstate.log))) as "#Hcown2".
    { rewrite /camp_own Hsfrole Hsfterm Hsflog -/F2. iExists F. iFrame "Hcown".
      iPureIntro. split_and!.
      - rewrite HF2. by apply prefix_app_r.
      - rewrite HLF HLF2. lia.
      - rewrite HF2 /plog_last last_app /=. done. }
    iAssert (lead_log_own γ sf (<[s.(pstate.term) := (γt, s.(pstate.base), s.(pstate.log))]> terms))
      with "[Htauth]" as "Htlog'".
    { rewrite /lead_log_own Hsfrole Hsfterm Hsfbase Hsflog.
      iExists γt, _, s.(pstate.log). iFrame "Htauth Hlf2".
      iSplit; first (iPureIntro; rewrite lookup_insert_eq //).
      rewrite big_sepM_singleton. iFrame "#".
      iPureIntro. split.
      - intros i [x Hx]. apply lookup_singleton_Some in Hx as [<- _].
        rewrite Hs2log /plog_last_index_Z length_app /=.
        rewrite Heidx /L /plog_last_index_Z. lia.
      - rewrite Hs2log. by apply prefix_app_r. }
    iAssert (matched_ok γ sf) as "#Hmatched'".
    { rewrite /matched_ok Hsfrole Hsfmatched Hsfterm.
      iApply big_sepM_intro. iIntros "!> %v %x %Hv".
      destruct (decide (v = id)) as [->|Hne].
      + rewrite Hmid in Hv. injection Hv as <-.
        iRight. iExists γa. by iFrame "#%".
      + rewrite (Hmoth v x Hne Hv). iLeft. done. }
    iAssert (acks_ok γ sf (<[(s.(pstate.term), plast_index s2) := ()]>
                            (<[(s.(pstate.term), plast_index s) := ()]> acks))) as "#Hacks_ok'".
    { rewrite /acks_ok Hsfrole //. }
    iAssert (commit_in γ (fp ++ sf.(pstate.log)) sf.(pstate.commit) sf.(pstate.term)) as "#Hcommit'".
    { rewrite Hsflog Hsfcommit Hsfterm -Hs2commit -Hs2term. iExact "Hcommit2". }
    iAssert (hists_ok γ sf (fp ++ sf.(pstate.log)) (<[(s.(pstate.term), plast_index s2) := ()]>
                            (<[(s.(pstate.term), plast_index s) := ()]> acks))) as "#Hhists'".
    { rewrite Hsflog. iExact "Hhists4". }
    iAssert (vlogs_ok γ sf (<[(s.(pstate.term), plast_index s2) := ()]>
                            (<[(s.(pstate.term), plast_index s) := ()]> acks)) vlogs) as "#Hvlogs'".
    { iExact "Hvlogs4". }
    iAssert (log_recs γ sf.(pstate.base) sf.(pstate.log)) as "#Hrecs'".
    { rewrite Hsfbase Hsflog -Hs2base. iExact "Hrecs2". }
    iAssert (base_ok γ sf.(pstate.base)) as "#Hbase'".
    { rewrite Hsfbase. iExact "Hbase". }
    iAssert ([∗ map] t ↦ γt ∈ <[s.(pstate.term) := (γt, s.(pstate.base), s.(pstate.log))]> terms,
               t ↪[γm]□ γt)%I as "#Htfrags'".
    { rewrite (big_sepM_insert _ terms) //. by iFrame "#". }
    iExists γm, _, γa, _, fp, γc, camps, γl, vlogs.
    iFrame "Hcommit' Hcown2 Hhists' Hvlogs' Hacks_ok' Hmatched' Hrecs' Hbase' Htfrags' Hafr2".
    iFrame "Hterms Hacks Hcamps Hvlogs Htlog' Hfrecs". iPureIntro. done.
  - split.
    + intros _. rewrite /psend_msgs /= Hs2vote. apply Hrok. congruence.
    + rewrite psend_msgs_role Hs2role. done.
Qed.

(** [step_beat]: a heartbeat carries the leadership, a commit index the
    leader has, and the [Match] it is bounded by. *)
Local Lemma own_raft_ghost_step_beat γ id s ms :
  s.(pstate.role) = role.Leader →
  Forall (heartbeat_ok id s) ms →
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (psend_msgs s ms).
Proof.
  intros Hrole Hms. iIntros "Hown". destruct_ghost.
  iDestruct (own_log_ghost_matched with "Hlg") as "#Hmatched".
  iEval (rewrite /matched_ok Hrole) in "Hmatched".
  iAssert (is_leader γ id s.(pstate.term)) as "#Hl".
  { rewrite /leader_wit Hrole. iFrame "#". }
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iDestruct (own_log_ghost_lead_full with "Hl Hlg") as "[(%fp & #Hp & #Hpf & #Hc) Hlg]"; first done.
  iDestruct (lead_full_intro with "Hp Hpf") as "#Hfl".
  iDestruct (lead_full_wf with "Hfl") as "[[%HwF _] #HrF]".
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    iApply big_sepL_intro. iIntros "!> %k %m %Hk".
    destruct (Forall_lookup_1 _ _ _ _ Hms Hk) as (Hty & Hfrom & Hterm & _ & Hcm & Hmatch).
    rewrite /is_message Hty Hfrom Hterm.
    iSplit; first iExact "Hl".
    iSplit.
    { iExists (fp ++ s.(pstate.log)). iSplit; first iExact "Hfl".
      iApply (commit_in_le with "HrF Hc"); done. }
    iSplit; last done.
    rewrite /match_of in Hmatch.
    destruct (s.(pstate.matched) !! m.(msg.to)) as [x|] eqn:Hx; simpl in Hmatch.
    + iExists x. iSplit; first done. iApply (big_sepM_lookup with "Hmatched"). done.
    + iExists (W64 0). iSplit; first done. iLeft. done.
  - rewrite /psend_msgs /=. iFrame "#".
  - rewrite /leader_wit /psend_msgs /=. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_send_apps]: as [step_win]'s broadcast. *)
Local Lemma own_raft_ghost_step_send_apps γ id s ms :
  s.(pstate.role) = role.Leader →
  Forall (repl_ok id s) ms →
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (psend_msgs s ms).
Proof.
  intros Hrole Hms. iIntros "Hown". destruct_ghost.
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iDestruct (own_log_ghost_base with "Hlg") as "#Hb".
  iAssert (is_leader γ id s.(pstate.term)) as "#Hl".
  { rewrite /leader_wit Hrole. iFrame "#". }
  iDestruct (own_log_ghost_lead_full with "Hl Hlg") as "[(%fp & #Hp & #Hpf & #Hc) Hlg]"; first done.
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    iApply big_sepL_intro. iIntros "!> %k %m %Hk".
    iApply (repl_ok_message _ id s _ fp with "Hl Hp Hpf Hrecs Hc Hb"); [by destruct Hok| |done].
    exact (Forall_lookup_1 _ _ _ _ Hms Hk).
  - rewrite /psend_msgs /=. iFrame "#".
  - rewrite /leader_wit /psend_msgs /=. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_prop_forward]: a proposal carries nothing. *)
Local Lemma own_raft_ghost_step_prop_forward γ id s m :
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs s
       [msg.mk mtype.Propose id s.(pstate.lead) (W64 0) m.(msg.reject)
          m.(msg.index) m.(msg.logterm) m.(msg.commit) m.(msg.rejecthint)
          m.(msg.entries)]).
Proof.
  iIntros "Hown". destruct_ghost.
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton. by iApply is_message_free.
  - rewrite /psend_msgs /=. iFrame "#".
  - rewrite /leader_wit /psend_msgs /=. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_app_resp]: the new [Match] is the old one or the acknowledgement
    the message carries. *)
Local Lemma own_raft_ghost_step_app_resp γ id s m x :
  m.(msg.ty) = mtype.AppResp →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Leader →
  m.(msg.reject) = false →
  s.(pstate.matched) !! m.(msg.from) = Some x →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (s <| pstate.matched :=
           <[m.(msg.from) := if decide (uint.Z x < uint.Z m.(msg.index))
                             then m.(msg.index) else x]> s.(pstate.matched) |>).
Proof.
  intros Hty Hterm Hrole Hrej Hx. iIntros "#Hm Hown". destruct_ghost.
  iAssert (is_acked γ m.(msg.from) s.(pstate.term) m.(msg.index)) as "#Hack".
  { rewrite /is_message Hty Hrej -Hterm. iFrame "#". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - simpl. iFrame "#".
  - simpl. iFrame "#".
  - rewrite /leader_wit /=. iFrame "#".
  - iDestruct (own_log_ghost_matched with "Hlg") as "#Hmatched".
    iDestruct (own_log_ghost_committed with "Hlg") as "#Hc".
    iApply (own_log_ghost_mono' with "Hlg [] []"); [log_mono_tac..| by left | |];
      last (iIntros (fp _) "_ #Hc'"; simpl; iExact "Hc'").
    rewrite /matched_ok /= Hrole.
    iEval (rewrite /matched_ok ?Hrole) in "Hmatched".
    iApply big_sepM_insert_2; last done.
    case_decide; first done.
    iApply (big_sepM_lookup with "Hmatched"). done.
Qed.

(** [step_commit]: a quorum of [Match]es at least [n] is [is_committed n]. *)
Local Lemma own_raft_ghost_step_commit γ id s n :
  s.(pstate.role) = role.Leader →
  uint.Z s.(pstate.commit) < uint.Z n →
  uint.Z n ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) →
  plog_term_at s.(pstate.base) s.(pstate.log) n = Some s.(pstate.term) →
  is_quorum γ.(re_cfg) (acked_by s n) →
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (s <| pstate.commit := n |>).
Proof.
  intros Hrole Hlt Hle Htm Hq. iIntros "Hown". destruct_ghost.
  iAssert (is_leader γ id s.(pstate.term)) as "#Hl".
  { rewrite /leader_wit Hrole. iFrame "#". }
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iDestruct (own_log_ghost_lead_full with "Hl Hlg") as "[(%fp0 & #Hp & #Hpf & _) Hlg]"; first done.
  iDestruct (lead_full_intro with "Hp Hpf") as "#Hfl".
  iPoseProof "Hpf" as (F0) "(_ & #Hfr0 & %Hfull0 & _)".
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - simpl. iFrame "#".
  - simpl. iFrame "#".
  - rewrite /leader_wit /=. iFrame "#".
  - iDestruct (own_log_ghost_matched with "Hlg") as "#Hmatched".
    iApply (own_log_ghost_mono' with "Hlg [] []"); [log_mono_tac..| right; simpl; lia | |].
    { rewrite /matched_ok /= Hrole. iEval (rewrite /matched_ok ?Hrole) in "Hmatched".
      iFrame "#". }
    iIntros (fp [Hf _]) "#Hfr _". simpl.
    iDestruct (full_ok_unique with "Hfr Hfr0") as %<-; [done|done|].
    iEval (rewrite /matched_ok ?Hrole) in "Hmatched".
    destruct Hok as (_ & Hbc & _).
    iRight. iExists s.(pstate.term), n, (fp ++ s.(pstate.log)).
    iSplit; last (iPureIntro; split_and!; [done|done|done]).
    iSplit; first (iPureIntro; rewrite (full_term_at s.(pstate.base)) //; lia).
    iSplit; first iExact "Hfl".
    iExists (acked_by s n). iSplit; first done.
    iApply big_sepS_intro. iIntros "!> %v %Hv".
    rewrite /acked_by elem_of_dom in Hv. destruct Hv as [x Hx].
    apply map_lookup_filter_Some in Hx as [Hx Hle'].
    iExists x. iSplit; first done.
    iApply (big_sepM_lookup with "Hmatched"). done.
Qed.

(** [step_app_stale]: back to follower of [m.from] in the same term, and
    acknowledge the commit index -- which needs no justification. *)
Local Lemma own_raft_ghost_step_app_stale γ id s m :
  m.(msg.ty) = mtype.App →
  m.(msg.from) ≠ id →
  s.(pstate.role) ≠ role.Leader →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs (padopt_leader s m.(msg.from))
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false s.(pstate.commit)
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hfid Hrole. iIntros "#Hm Hown". destruct_ghost.
  iAssert (⌜ m.(msg.from) ≠ W64 0 ⌝)%I as %Hfnz.
  { rewrite /is_message Hty. iDestruct "Hm" as "(_ & _ & _ & $)". }
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iDestruct (own_log_ghost_mono γ id s (padopt_leader s m.(msg.from)) with "Hlg") as "Hlg";
    [log_mono_tac..|].
  iMod (own_log_ghost_ack _ _ _ s.(pstate.commit) with "[] [] Hlg") as "[Hlg #Hack]".
  { iIntros ([_ ?]). simpl in *. lia. }
  { iIntros (fp [Hf Hw]) "#Hfr #Hc". iApply (hist_of_commit with "[] Hc").
    - by eapply full_wf.
    - rewrite /bnd /= decide_False; [lia|]. naive_solver.
    - iApply (log_recs_full with "Hfr Hrecs"). done. }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_app_reject]: back to follower of [m.from]; a rejection carries
    nothing. *)
Local Lemma own_raft_ghost_step_app_reject γ id s m hint hintterm :
  m.(msg.ty) = mtype.App →
  m.(msg.from) ≠ id →
  s.(pstate.role) ≠ role.Leader →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs (padopt_leader s m.(msg.from))
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) true m.(msg.index)
          hintterm (W64 0) hint []]).
Proof.
  intros Hty Hfid Hrole. iIntros "#Hm Hown". destruct_ghost.
  iAssert (⌜ m.(msg.from) ≠ W64 0 ⌝)%I as %Hfnz.
  { rewrite /is_message Hty. iDestruct "Hm" as "(_ & _ & _ & $)". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. done.
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_heartbeat]: back to follower of [m.from]; the new commit index is
    the old one or the heartbeat's, which carries [is_committed] and which
    the rule's premise puts within the log. *)
Local Lemma own_raft_ghost_step_heartbeat γ id s m :
  m.(msg.ty) = mtype.Heartbeat →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  m.(msg.from) ≠ id →
  s.(pstate.role) ≠ role.Leader →
  uint.Z m.(msg.commit) ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs
       (padopt_leader s m.(msg.from)
          <| pstate.commit := plog_commit_to s.(pstate.commit) m.(msg.commit) |>)
       [msg.plain mtype.HeartbeatResp id m.(msg.from) s.(pstate.term) false]).
Proof.
  intros Hty Hto Hterm Hfid Hrole Hcm. iIntros "#Hm Hown". destruct_ghost.
  iAssert ((∃ Fl, lead_full γ s.(pstate.term) Fl ∗
              commit_in γ Fl m.(msg.commit) s.(pstate.term)) ∗
           (∃ i, ⌜ uint.Z m.(msg.commit) ≤ uint.Z i ⌝ ∗ is_acked γ id s.(pstate.term) i) ∗
           ⌜ m.(msg.from) ≠ W64 0 ⌝)%I
    as "((%Fl & #Hfl & #Hmc) & (%i & %Hi & #Hack) & %Hfnz)".
  { rewrite /is_message Hty -Hto -Hterm. iDestruct "Hm" as "(_ & $ & $ & $)". }
  (* above the commit index, the log agrees with the leader's at [m.commit] *)
  iDestruct (own_log_ghost_ack_agree with "Hlg Hack") as "#Hagree".
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. done.
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono' with "Hlg [] []"); [log_mono_tac..| | | | |].
    + rewrite /= /plog_commit_to. case_decide; lia.
    + bnd_tac.
    + rewrite /= /plog_commit_to. case_decide; [by right|by left].
    + rewrite /matched_ok /=. done.
    + iIntros (fp [Hf Hw]) "#Hfr #Hc". rewrite /= /plog_commit_to.
      case_decide as Hlt; last iExact "Hc".
      assert (Hci : uint.Z s.(pstate.commit) < uint.Z i) by lia.
      iDestruct ("Hagree" $! (conj Hrole Hci)) as "#Ha".
      iDestruct (ack_agree_full _ _ _ fp with "Ha") as (X) "[#HX [%HsX %HXi]]";
        [done|destruct Hok as (_ & ? & _); lia|].
      iDestruct (log_recs_full with "Hfr Hrecs") as "#HrF"; first done.
      pose proof (full_wf _ _ _ Hf Hw) as HwF.
      iDestruct (lead_full_wf with "HX") as "[[%HwX _] #HrX]".
      iDestruct (full_match _ _ _ i HwX HwF HsX HXi with "HrX HrF") as %Hm.
      iDestruct "Hmc" as "[%H0 | (%t & %n & %G & #Hq & %Hc & %Ht & %HG)]"; [word|].
      iDestruct (cq_full with "Hq") as "[%HwG _]".
      iPoseProof "Hq" as "(%Hn & _)".
      assert (HsG : is_Some (plog_term_at base0 G m.(msg.commit))).
      { apply (full_term_at_some _ _ n); [by eexists|lia]. }
      iDestruct (lead_full_agree _ _ X Fl m.(msg.commit) with "HX Hfl") as %HXl.
      { apply (full_term_at_some _ _ i); [done|lia]. }
      { rewrite -HG. done. }
      iRight. iExists t, n, G. iFrame "Hq". iPureIntro. split_and!; [done|done|].
      rewrite HG -HXl. apply Hm. lia.
Qed.

(** [step_app_accept].  The new log is the old one cut at the first
    conflict, if any, and the batch appended ([plog_maybe_append_inv]); the
    batch is the leader's ([is_message]'s [lead_prefix]).  So the new log
    has records (the old ones below the cut; the leader's above, whose
    predecessor terms are the batch's, which the new log has:
    [plog_maybe_append_batch], [plog_prefix_batch]); every justified
    acknowledgement of this term is below the cut ([ack_agree_term]: the
    old log agrees with the leader there, and the cut is where it does
    not); and the new acknowledgement of [lastnewi] is justified by the
    batch itself. *)
Local Lemma own_raft_ghost_step_app_accept γ id s m lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) ≤ uint.Z m.(msg.index) →
  plog_maybe_append s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs
       (padopt_leader s m.(msg.from) <| pstate.log := es' |>
          <| pstate.commit := plog_commit_to s.(pstate.commit)
                                (if decide (uint.Z m.(msg.commit) < uint.Z lastnewi)
                                 then m.(msg.commit) else lastnewi) |>)
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false lastnewi
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hfid Hterm Hrole Hcidx Happ. iIntros "#Hm Hown". destruct_ghost.
  iAssert (⌜ app_payload_ok m ⌝ ∗
           (∃ bL l fpL, lead_prefix γ m.(msg.from) m.(msg.term) bL l ∗
              ⌜ plog_term_at bL l m.(msg.index) = Some m.(msg.logterm) ∧
                m.(msg.entries) `prefix_of` plog_from bL l (word.add m.(msg.index) (W64 1)) ⌝ ∗
              lpfull γ m.(msg.from) m.(msg.term) bL l fpL ∗
              commit_in γ (fpL ++ l) m.(msg.commit) m.(msg.term)) ∗
           ⌜ m.(msg.from) ≠ W64 0 ⌝)%I
    as "(%Hpay & (%bL & %l' & %fpL & #Hp' & [%Hprev' %Hpre'] & #Hpf' & #Hmc) & %Hfnz)".
  { iEval (rewrite /is_message Hty) in "Hm". iDestruct "Hm" as "($ & _ & $ & $)". }
  iEval (rewrite Hterm) in "Hp' Hpf' Hmc".
  iDestruct (lead_full_intro with "Hp' Hpf'") as "#HLf".
  iDestruct (lead_full_wf with "HLf") as "[[%HwLf _] #HrLf]".
  iPoseProof "Hpf'" as (FL0) "(_ & _ & %HfL & _)".
  set (Lf := fpL ++ l').
  destruct Hpay as (Hwfb & Hnw & _).
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iDestruct (own_log_ghost_wf with "Hlg") as %Hwl.
  destruct Hok as (Hwf & Hbc & Hcl).
  pose proof (plog_maybe_append_inv _ _ _ _ _ _ Hwfb Hnw Happ) as (Hmatch & Hli & Hcase).
  simpl in Hli, Hcase.
  destruct (plog_maybe_append_wf_r _ _ _ _ _ _ Hwf Hwfb Hnw Happ) as (Hwf' & Hlast').
  pose proof (plog_maybe_append_batch _ _ _ _ _ _ Hwfb Hnw Happ) as Hbatch.
  pose proof (plog_prefix_batch bL l' (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries) Hnw Hprev' Hpre') as Hlb.
  simpl in Hbatch, Hlb.
  pose proof (plog_term_at_Some_range _ _ _ _ Hmatch) as [Hpb Hpl]. simpl in Hpb, Hpl.
  pose proof (plog_term_at_Some_range _ _ _ _ Hprev') as [HbL _].
  pose proof (word.unsigned_range m.(msg.index)).
  (* the batch, as a log after [(logterm, index)], is the leader's and the
     new log's on [[index, index + |entries|]] *)
  assert (Hagree : ∀ j : w64, uint.Z m.(msg.index) ≤ uint.Z j ≤
                     uint.Z m.(msg.index) + Z.of_nat (length m.(msg.entries)) →
                   plog_term_at s.(pstate.base) es' j = plog_term_at bL l' j ∧
                   is_Some (plog_term_at bL l' j)).
  { intros j Hj. rewrite (Hbatch j Hj) (Hlb j Hj). split; [done|].
    apply plog_term_at_in_range. rewrite /plog_last_index_Z /=. lia. }
  set (c' := plog_commit_to s.(pstate.commit)
               (if decide (uint.Z m.(msg.commit) < uint.Z lastnewi)
                then m.(msg.commit) else lastnewi)).
  assert (Hc'1 : uint.Z s.(pstate.commit) ≤ uint.Z c')
    by (rewrite /c' /plog_commit_to; case_decide; lia).
  assert (Hc'2 : uint.Z c' ≤ uint.Z lastnewi ∨ c' = s.(pstate.commit)).
  { rewrite /c' /plog_commit_to. case_decide; [left; case_decide; lia|by right]. }
  iAssert (log_recs γ s.(pstate.base) es') as "#Hrecs'".
  { destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & Hes')];
      [iExact "Hrecs"|].
    iDestruct (lead_prefix_wf with "Hp'") as "[%Hwfl #Hrl]".
    rewrite /log_recs. iApply big_sepL_intro. iIntros "!> %k %x %Hk".
    case_decide as Hr; [|done].
    set (n := Z.to_nat (uint.Z e.(raftpb.Entry.Index') - uint.Z s.(pstate.base).(raft.entryID.index') - 1)).
    assert (Hn : (n ≤ length s.(pstate.log))%nat) by (rewrite /plog_last_index_Z in Hend; lia).
    rewrite Hes' in Hk.
    destruct (decide (k < n)%nat) as [Hkn|Hkn].
    - rewrite Hes'.
      rewrite lookup_app_l in Hk; [|rewrite length_take; lia].
      rewrite lookup_take_lt in Hk; [|done].
      iDestruct (big_sepL_lookup with "Hrecs") as "H"; first exact Hk.
      rewrite decide_True //. iDestruct "H" as (pt Hpt) "Hx". iExists pt. iFrame "Hx".
      iPureIntro. rewrite -Hpt. apply plog_cut_keep; [lia|].
      pose proof (word.unsigned_range s.(pstate.base).(raft.entryID.index')).
      unfold n in Hkn. rewrite /pidx word.unsigned_of_Z_nowrap; lia.
    - rewrite lookup_app_r in Hk; [|rewrite length_take; lia].
      rewrite length_take Nat.min_l in Hk; [|done]. rewrite lookup_drop in Hk.
      set (kk := (d + (k - n))%nat) in Hk.
      apply lookup_lt_Some in Hd as Hdlen.
      pose proof (lookup_lt_Some _ _ _ Hk) as Hkk.
      (* [x] is the leader's entry at [index + 1 + kk] *)
      pose proof (prefix_lookup_Some _ _ _ _ Hk Hpre') as Hx'.
      rewrite /plog_from lookup_drop in Hx'.
      set (p := (Z.to_nat (uint.Z (word.add m.(msg.index) (W64 1))
                           - uint.Z bL.(raft.entryID.index') - 1) + kk)%nat) in Hx'.
      assert (Hadd : uint.Z (word.add m.(msg.index) (W64 1)) = uint.Z m.(msg.index) + 1) by word.
      iDestruct (big_sepL_lookup with "Hrl") as "H"; first exact Hx'.
      rewrite decide_True; [|lia].
      iDestruct "H" as (pt Hpt) "Hx". iExists pt. iFrame "Hx". iPureIntro.
      pose proof (word.unsigned_range s.(pstate.base).(raft.entryID.index')).
      assert (Hpj : pidx s.(pstate.base) k = W64 (uint.Z m.(msg.index) + Z.of_nat kk)).
      { rewrite /pidx. f_equal. unfold kk, n in *. lia. }
      assert (Hpj' : pidx bL p = W64 (uint.Z m.(msg.index) + Z.of_nat kk)).
      { rewrite /pidx. f_equal. unfold p, kk, n in *. lia. }
      unfold kk, n in Hkk.
      rewrite Hpj' in Hpt. rewrite Hpj -Hpt.
      refine (proj1 (Hagree _ _)). rewrite word.unsigned_of_Z_nowrap; lia. }
  iAssert (□ (⌜ s.(pstate.term) = s.(pstate.term) ⌝ -∗ ∀ i,
             ⌜ uint.Z c' < uint.Z i ⌝ -∗
             ack_agree γ s.(pstate.base) s.(pstate.log) s.(pstate.term) i -∗
             ack_agree γ s.(pstate.base) es' s.(pstate.term) i))%I as "#Hkeep".
  { iIntros "!> _ %i %Hi #Ha".
    destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & Hes')];
      [iExact "Ha"|].
    apply lookup_lt_Some in Hd as Hdlen.
    (* every justified acknowledgement is below the cut *)
    destruct (decide (uint.Z i < uint.Z e.(raftpb.Entry.Index'))) as [Hlt|Hge]; last first.
    { iDestruct (ack_agree_term _ _ _ _ i _ bL l' e.(raftpb.Entry.Index') Hwf with "Hrecs Ha Hp'")
        as %Hj; [lia|lia|lia|exact (proj2 (Hagree e.(raftpb.Entry.Index') ltac:(lia)))|].
      exfalso. apply Hnm.
      rewrite /plog_matches /ent_id /= Hj (Hlb e.(raftpb.Entry.Index') ltac:(lia)).
      eapply plog_term_at_lookup; [exact Hd|]. simpl. lia. }
    iDestruct "Ha" as (Hil ldr bL0 l0) "(#Hp0 & %Hs0 & #Hpf0)".
    rewrite Hes'. iSplit.
    - iPureIntro. rewrite plog_cut_last; [|lia]. rewrite length_drop. lia.
    - iExists ldr, bL0, l0. iFrame "Hp0 Hpf0". iPureIntro. destruct Hs0 as [? Heq0].
      split; [done|]. rewrite Heq0. symmetry. apply plog_cut_keep; lia. }
  (* the new log, as a full log: the old one below the batch, the leader's
     on the batch, nothing after it when it was cut *)
  assert (Hlast'' : plog_last_index_Z s.(pstate.base) es' < 2 ^ 64 ∧
                    (es' ≠ s.(pstate.log) → plog_last_index_Z s.(pstate.base) es' = uint.Z lastnewi)).
  { destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & Hes')].
    - split; [by apply plog_wf_range|done].
    - rewrite Hes' plog_cut_last; [|lia]. rewrite length_drop.
      apply lookup_lt_Some in Hd. split; lia. }
  assert (Hwl' : plog_wf s.(pstate.base) es').
  { apply plog_wf_r_wf; [done|apply Hlast'']. }
  assert (Hfull_new : ∀ fp, full_ok s.(pstate.base) fp →
      (∀ j : w64, uint.Z j ≤ uint.Z m.(msg.index) →
         plog_term_at base0 (fp ++ es') j = plog_term_at base0 (fp ++ s.(pstate.log)) j) ∧
      (∀ j : w64, uint.Z m.(msg.index) ≤ uint.Z j ≤ uint.Z lastnewi →
         plog_term_at base0 (fp ++ es') j = plog_term_at base0 Lf j ∧
         is_Some (plog_term_at base0 Lf j))).
  { intros fp Hf. split.
    - intros j Hj. destruct (decide (uint.Z j < uint.Z s.(pstate.base).(raft.entryID.index'))).
      + rewrite !(full_term_at_le s.(pstate.base) fp) //; lia.
      + rewrite !(full_term_at s.(pstate.base) fp) //; [|lia..].
        destruct (decide (uint.Z j = uint.Z m.(msg.index))) as [Hjm|Hjm].
        * assert (j = m.(msg.index)) as -> by word.
          destruct (Hagree m.(msg.index)) as [Heq _]; [lia|].
          rewrite Heq Hprev'. symmetry. exact Hmatch.
        * destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & Hes')]; [done|].
          rewrite Hes'. apply plog_cut_keep; lia.
    - intros j Hj. destruct (Hagree j ltac:(lia)) as [Heq Hs].
      rewrite (full_term_at s.(pstate.base) fp) //; try lia.
      rewrite /Lf (full_term_at bL fpL) //; try lia. }
  iDestruct (own_log_ghost_base with "Hlg") as "#Hb".
  set (s' := padopt_leader s m.(msg.from) <| pstate.log := es' |> <| pstate.commit := c' |>).
  assert (Hbnd' : bnd s' = uint.Z s.(pstate.term) + 1).
  { rewrite /bnd /= decide_False //. naive_solver. }
  iPoseProof (own_log_ghost_upd γ id s s'
               with "Hlg [] Hrecs' [] [Hb] []") as "Hlg"; [log_mono_tac..| | | | | | | ].
  { rewrite Hbnd'. rewrite /bnd. case_decide; lia. }
  { rewrite /log_ok /=. split_and!; [done|lia|].
    destruct Hc'2 as [?| ->]; [lia|]. lia. }
  { iModIntro. iIntros "_ %i %Hi #Ha". simpl in Hi. iApply ("Hkeep" with "[//] [%] Ha"). done. }
  { rewrite /matched_ok /=. done. }
  { simpl. iExact "Hb". }
  { iIntros (fp (Hf & Hw & Htle)) "#Hfr #Hc".
    destruct (Hfull_new fp Hf) as [Hlow Hmid].
    iDestruct (log_recs_full with "Hfr Hrecs'") as "#HrF'"; first done.
    iDestruct (log_recs_full with "Hfr Hrecs") as "#HrF"; first done.
    pose proof (full_wf _ _ _ Hf Hwl') as HwF'.
    pose proof (full_wf _ _ _ Hf Hw) as HwF.
    destruct (Hmid lastnewi ltac:(lia)) as [Hli' Hsli].
    iDestruct (full_match _ _ _ lastnewi HwLf HwF' Hsli (eq_sym Hli') with "HrLf HrF'") as %HmL.
    iPoseProof "Hpf'" as (?) "(_ & _ & _ & _ & _ & %HtL)".
    iExists fp. simpl. iSplit; [iPureIntro; split_and!|iSplit; [iExact "Hfr"|iSplit]].
    - done.
    - done.
    - (* terms: the old log's, or the leader's *)
      intros j x Hx. split; [|done].
      destruct (decide (uint.Z j ≤ uint.Z m.(msg.index))) as [Hjm|Hjm].
      + rewrite Hlow // in Hx. by destruct (Htle j x Hx).
      + destruct (decide (uint.Z j ≤ uint.Z lastnewi)) as [HjL|HjL].
        * rewrite (proj1 (Hmid j ltac:(lia))) in Hx. by apply (HtL j x).
        * destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & Hes')].
          { by destruct (Htle j x Hx). }
          exfalso. pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ Hr].
          rewrite (full_last_index s.(pstate.base)) // in Hr.
          apply lookup_lt_Some in Hd.
          rewrite Hes' plog_cut_last in Hr; [|lia]. rewrite length_drop in Hr. lia.
    - intros Hr. exfalso. by apply Hr.
    - (* the commit fact *)
      rewrite /s' /c' /plog_commit_to /=. case_decide as Hlt.
      + iApply (commit_in_agree _ Lf); [done| |].
        { symmetry. apply HmL. case_decide; lia. }
        iApply (commit_in_le with "HrLf Hmc"); [done|]. case_decide; lia.
      + iApply (commit_in_agree with "Hc"); [done|]. apply Hlow. lia.
    - (* histories *)
      iIntros "!> %t %i %Ht #Hh". rewrite Hbnd'.
      destruct Hcase as [[-> _] | (d & e & Hd & Hnm & Hbefore & Hei & Hend & Hes')].
      { iApply (hist_mono with "Hh"). rewrite /bnd. case_decide; lia. }
      pose proof (Hwfb _ _ Hd) as Hed. simpl in Hed.
      apply lookup_lt_Some in Hd as Hdlen.
      iApply (hist_replace _ _ _ Lf t i s.(pstate.term) _ _ (uint.Z e.(raftpb.Entry.Index'))
                e.(raftpb.Entry.Index') lastnewi with "HLf Hh").
      + rewrite /bnd. case_decide; lia.
      + done.
      + lia.
      + lia.
      + lia.
      + intros j Hj.
        destruct (decide (uint.Z j < uint.Z s.(pstate.base).(raft.entryID.index'))).
        * rewrite !(full_term_at_le s.(pstate.base) fp) //; lia.
        * rewrite !(full_term_at s.(pstate.base) fp) //; [|lia..].
          rewrite Hes'. apply plog_cut_keep; lia.
      + intros j Hj. apply Hmid. lia.
      + rewrite (full_term_at s.(pstate.base) fp) //; [|lia].
        rewrite /Lf (full_term_at bL fpL) //; [|lia].
        rewrite (Hlb e.(raftpb.Entry.Index')); [|lia].
        rewrite (plog_term_at_lookup _ _ _ d e Hd); [|simpl; lia].
        exact Hnm.
      + intros j Hj. apply plog_term_at_None_range. right.
        rewrite (full_last_index s.(pstate.base)) //.
        rewrite Hes' plog_cut_last; [|lia]. rewrite length_drop. lia. }
  iMod (own_log_ghost_ack _ _ _ lastnewi with "[] [] Hlg") as "[Hlg #Hack]".
  { iIntros ([_ _]). simpl. iSplit; first (iPureIntro; lia).
    iExists m.(msg.from), bL, l'. iFrame "Hp'". iSplit; last (iExists fpL; iFrame "Hpf'").
    iPureIntro. destruct (Hagree lastnewi ltac:(lia)) as [Heq Hs]. split; [done|]. by rewrite Heq. }
  { iIntros (fp [Hf Hw]) "#Hfr _". simpl.
    destruct (Hfull_new fp Hf) as [_ Hmid].
    iDestruct (log_recs_full with "Hfr Hrecs'") as "#HrF'"; first done.
    destruct (Hmid lastnewi ltac:(lia)) as [Hli' Hsli].
    iApply (hist_of_agree _ _ Lf with "HrF'"); [by eapply full_wf|done|done|].
    iLeft. iExists s.(pstate.term). iFrame "HLf". iPureIntro. rewrite Hbnd'. lia. }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** Freezing a batch of stamped entries into the leader's term log: their
    indices are past everything in it ([lead_log_own]'s bound) and do not
    wrap.  Each is frozen with the predecessor term [ptf k]. *)
Local Lemma term_log_insert_stamped γt (M : gmap w64 (raftpb.Entry.t * w64)) (T : w64) (L : Z)
    (ents : list raftpb.Entry.t) (ptf : nat → w64) :
  0 ≤ L → L + Z.of_nat (length ents) < 2 ^ 64 →
  (∀ i, is_Some (M !! i) → uint.Z i ≤ L) →
  ghost_map_auth γt 1 M -∗ ([∗ map] i ↦ e ∈ M, i ↪[γt]□ e) ==∗
  ∃ M' : gmap w64 (raftpb.Entry.t * w64),
    ghost_map_auth γt 1 M' ∗ ([∗ map] i ↦ e ∈ M', i ↪[γt]□ e) ∗
    ⌜ ∀ i, is_Some (M' !! i) → uint.Z i ≤ L + Z.of_nat (length ents) ⌝ ∗
    [∗ list] k ↦ e ∈ imap (stamp T (W64 L)) ents, e.(raftpb.Entry.Index') ↪[γt]□ (e, ptf k).
Proof.
  iIntros (HL Hnw Hdom) "Hauth #Hfr".
  iInduction ents as [|x ents] "IH" using rev_ind forall (Hnw).
  - iModIntro. iExists M. iFrame "Hauth Hfr". simpl. iSplit; last done.
    iPureIntro. intros i Hi. specialize (Hdom i Hi). lia.
  - rewrite length_app /= in Hnw.
    iMod ("IH" with "[%] Hauth") as (M') "(Hauth & #Hfr' & %Hdom' & #Hents)"; first lia.
    set (k := length ents).
    set (e := stamp T (W64 L) k x).
    assert (Hidx : uint.Z e.(raftpb.Entry.Index') = L + 1 + k).
    { rewrite /e /stamp /=. apply stamp_index_eq; lia. }
    assert (Hfresh : M' !! e.(raftpb.Entry.Index') = None).
    { destruct (M' !! e.(raftpb.Entry.Index')) eqn:Hm; last done.
      exfalso. specialize (Hdom' _ ltac:(by eexists)). lia. }
    iMod (ghost_map_insert_persist _ (e, ptf k) Hfresh with "Hauth") as "[Hauth #Hnew]".
    iModIntro. iExists (<[e.(raftpb.Entry.Index') := (e, ptf k)]> M'). iFrame "Hauth".
    iSplit.
    { rewrite big_sepM_insert //. by iFrame "#". }
    iSplit.
    { iPureIntro. intros i [y Hy]. rewrite length_app /=.
      destruct (decide (i = e.(raftpb.Entry.Index'))) as [->|Hne].
      - lia.
      - rewrite lookup_insert_ne // in Hy. specialize (Hdom' i ltac:(by eexists)). lia. }
    rewrite imap_app big_sepL_app /=. iFrame "#".
    rewrite length_imap !Nat.add_0_r. iFrame "#".
Qed.

(** [step_propose]: the stamped entries go into the leader's term log
    ([term_log_insert_stamped]), which gives each its [is_entry_r] (the
    first after the old last entry, the rest after each other); the
    self-acknowledgement is the node's own to allocate. *)
Local Lemma own_raft_ghost_step_propose γ id s ents :
  s.(pstate.role) = role.Leader →
  plog_last_index_Z s.(pstate.base) s.(pstate.log) + Z.of_nat (length ents) < 2 ^ 64 →
  let s' := pappend s (imap (stamp s.(pstate.term) (plast_index s)) ents) in
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (psend_msgs s' [pself_ack id s']).
Proof.
  intros Hrole Hnw s'.
  iIntros "Hown". destruct_ghost.
  iAssert (is_leader γ id s.(pstate.term)) as "#Hl".
  { rewrite /leader_wit Hrole. iFrame "#". }
  iDestruct "Hlg" as (γm terms γa acks fp γc camps γl vlogs) "Hlg". iNamed "Hlg".
  iEval (rewrite /lead_log_own Hrole) in "Htlog".
  iDestruct "Htlog" as (γt M l0 Hγt) "(Htauth & #Htel & %Hdom & %Hpre & #Hlf)".
  iPoseProof "Hcown" as "Hcown0". iEval (rewrite /camp_own Hrole) in "Hcown0".
  iDestruct "Hcown0" as (F0) "[#Hc0 (%HF0pre & %HF0len & %HlastT)]".
  destruct Hlog_ok as (Hwf & Hbc & Hcl).
  destruct Hfull as (Hfp & Hwl & Htle).
  set (L := plog_last_index_Z s.(pstate.base) s.(pstate.log)).
  pose proof (plog_last_index_Z_nonneg s.(pstate.base) s.(pstate.log)) as HL.
  set (pt0 := (plog_last s.(pstate.base) s.(pstate.log)).(raft.entryID.term')).
  assert (Hpt0 : pt0 = s.(pstate.term)) by (rewrite /pt0 -(full_last _ fp) //).
  assert (HLF : plog_last_index_Z base0 (fp ++ s.(pstate.log)) = L) by (by apply full_last_index).
  set (ptf := λ k : nat, if decide (k = 0%nat) then pt0 else s.(pstate.term)).
  assert (Hptf : ∀ k, ptf k = s.(pstate.term)) by (intros k; rewrite /ptf; case_decide; done).
  iMod (term_log_insert_stamped γt M s.(pstate.term) L ents ptf HL Hnw Hdom
          with "Htauth Htel") as (M') "(Htauth & #Htel' & %Hdom' & #Hnew)".
  iAssert (is_term_log γ id s.(pstate.term) γt s.(pstate.base) l0) as "#Htl".
  { iExists γm. iFrame "%". iApply (big_sepM_lookup with "Htfrags"). done. }
  set (nw := imap (stamp s.(pstate.term) (W64 L)) ents).
  assert (Hs'log : s'.(pstate.log) = s.(pstate.log) ++ nw) by reflexivity.
  assert (Hs'role : s'.(pstate.role) = s.(pstate.role)) by reflexivity.
  assert (Hs'term : s'.(pstate.term) = s.(pstate.term)) by reflexivity.
  assert (Hs'base : s'.(pstate.base) = s.(pstate.base)) by reflexivity.
  assert (Hs'cm : s'.(pstate.commit) = s.(pstate.commit)) by reflexivity.
  assert (Hs'bnd : bnd s' = bnd s) by reflexivity.
  assert (Hnwk : ∀ (k : nat) x, nw !! k = Some x →
                   uint.Z x.(raftpb.Entry.Index') = L + 1 + k ∧
                   x.(raftpb.Entry.Term') = s.(pstate.term)).
  { intros k x Hk. rewrite /nw list_lookup_imap in Hk.
    destruct (ents !! k) as [y|] eqn:Hy; simpl in Hk; [|done]. injection Hk as <-.
    apply lookup_lt_Some in Hy. split; [|done].
    rewrite /stamp /=. apply stamp_index_eq; lia. }
  assert (Hlen : length nw = length ents) by (rewrite /nw length_imap //).
  iAssert (log_recs γ s.(pstate.base) (s.(pstate.log) ++ nw)) as "#Hrecs'".
  { rewrite /log_recs big_sepL_app. iSplit.
    - iApply (big_sepL_impl with "Hrecs"). iIntros "!> %k %x %Hk H".
      case_decide as Hr; [|done]. iDestruct "H" as (pt Hpt) "Hx". iExists pt. iFrame "Hx".
      iPureIntro. rewrite plog_term_at_app_l; [done|].
      apply lookup_lt_Some in Hk. rewrite /pidx word.unsigned_of_Z_nowrap.
      + rewrite /plog_last_index_Z. lia.
      + pose proof (word.unsigned_range s.(pstate.base).(raft.entryID.index')). lia.
    - iApply (big_sepL_impl with "Hnew"). iIntros "!> %k %x %Hk #Hx".
      case_decide as Hr; [|done]. destruct (Hnwk k x Hk) as [Hxi Hxt].
      pose proof (lookup_lt_Some _ _ _ Hk) as Hklt.
      iExists (ptf k). iSplit.
      + iPureIntro.
        assert (Hp : pidx s.(pstate.base) (length s.(pstate.log) + k) = W64 (L + k)).
        { rewrite /pidx /L /plog_last_index_Z. f_equal. lia. }
        rewrite Hp /ptf. destruct (decide (k = 0%nat)) as [->|Hk0].
        * rewrite Z.add_0_r plog_term_at_app_l; last first.
          { rewrite word.unsigned_of_Z_nowrap; [rewrite /L; lia|lia]. }
          apply plog_term_at_last_r; [done|]. rewrite -/L. lia.
        * rewrite plog_term_at_app_r; last (rewrite word.unsigned_of_Z_nowrap; [rewrite -/L; lia|lia]).
          rewrite -/L word.unsigned_of_Z_nowrap; [|lia].
          destruct (lookup_lt_is_Some_2 nw (k - 1) ltac:(lia)) as [y Hy].
          replace (Z.to_nat (L + k - L - 1)) with (k - 1)%nat by lia.
          rewrite Hy /=. destruct (Hnwk _ _ Hy) as [_ ->]. done.
      + iExists id, γt, s.(pstate.base), l0, F0. rewrite Hxt. iFrame "#".
        iPureIntro. rewrite /pt_ok Hxi Hptf. rewrite HLF in HF0len. split_and!; [lia|lia|lia|done]. }
  iAssert (lead_frags γt l0 (s.(pstate.log) ++ nw)) as "#Hlf'".
  { rewrite /lead_frags big_sepL_app. iSplit; [iExact "Hlf"|].
    iApply (big_sepL_impl with "Hnew"). iIntros "!> %k %x %Hk #Hx".
    apply prefix_length in Hpre. rewrite decide_True; [|lia]. iExists (ptf k). iFrame "Hx". }
  (* the new full log extends the old one, with entries of the term *)
  set (F' := fp ++ s'.(pstate.log)).
  assert (HF' : F' = (fp ++ s.(pstate.log)) ++ nw) by (rewrite /F' Hs'log app_assoc //).
  assert (Hwl' : plog_wf s.(pstate.base) (s.(pstate.log) ++ nw)).
  { apply plog_wf_app. split; [done|]. intros k x Hk. destruct (Hnwk _ _ Hk) as [Hxi _].
    rewrite Hxi /L /plog_last_index_Z. lia. }
  assert (HkeepF : ∀ j : w64, is_Some (plog_term_at base0 (fp ++ s.(pstate.log)) j) →
                     plog_term_at base0 F' j = plog_term_at base0 (fp ++ s.(pstate.log)) j).
  { intros j [x Hx]. rewrite HF'. apply plog_term_at_app_l.
    by pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ ?]. }
  assert (HtF' : terms_le s' F').
  { intros j x Hx. rewrite Hs'term Hs'role Hrole. split; [|done].
    pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ Hj].
    destruct (decide (uint.Z j ≤ L)) as [Hle|Hgt].
    - rewrite HF' plog_term_at_app_l in Hx; [|lia]. by destruct (Htle _ _ Hx).
    - rewrite HF' plog_term_at_app_r in Hx; [|lia].
      destruct (nw !! _) as [y|] eqn:Hy; [|done]. simpl in Hx. injection Hx as <-.
      destruct (Hnwk _ _ Hy) as [_ ->]. lia. }
  iAssert (camp_own γ id s' F') as "#Hcown'".
  { rewrite /camp_own Hs'role Hrole Hs'term. iExists F0. iFrame "Hc0". iPureIntro. split_and!.
    - rewrite HF'. by apply prefix_app_r.
    - rewrite HF' /plog_last_index_Z length_app. rewrite /plog_last_index_Z in HF0len. lia.
    - rewrite HF' /plog_last last_app. destruct (list.last nw) as [y|] eqn:Hy.
      + rewrite last_lookup in Hy. destruct (Hnwk _ _ Hy) as [_ ?]. done.
      + done. }
  iAssert (hists_ok γ s' F' acks) as "#Hhists'".
  { iApply (big_sepM_impl with "Hhists"). iIntros "!> %k %u %Hk #Hk". rewrite Hs'bnd.
    iApply (hist_keep with "Hk"). intros j _ Hj. by apply HkeepF. }
  iAssert (commit_in γ F' s'.(pstate.commit) s'.(pstate.term)) as "#Hcommit'".
  { rewrite Hs'cm Hs'term. iApply (commit_in_agree with "Hcommit"); [done|].
    apply HkeepF. apply plog_term_at_in_range. rewrite base0_index HLF. word. }
  iAssert (lead_log_own γ s' terms) with "[Htauth]" as "Htlog'".
  { rewrite /lead_log_own Hs'role Hs'term Hs'base Hs'log Hrole.
    iExists γt, M', l0. iFrame "Htauth Htel' Hlf'". iSplit; first done.
    iPureIntro. split.
    - intros i Hi. specialize (Hdom' i Hi).
      rewrite /plog_last_index_Z length_app Hlen. rewrite /L /plog_last_index_Z in Hdom'. lia.
    - by apply prefix_app_r. }
  assert (Hlog_ok' : log_ok s').
  { rewrite /log_ok Hs'base Hs'log Hs'cm.
    split_and!; [|done|].
    - by apply plog_wf_wf_r.
    - rewrite /plog_last_index_Z length_app. rewrite /plog_last_index_Z in Hcl. lia. }
  iAssert (matched_ok γ s') as "#Hmatched'".
  { iApply (matched_ok_eq with "Hmatched"); done. }
  iAssert (vlogs_ok γ s' acks vlogs) as "#Hvlogs'".
  { rewrite /vlogs_ok Hs'term. iExact "Hvlogs_ok". }
  iAssert (acks_ok γ s' acks) as "#Hacks_ok'".
  { rewrite /acks_ok Hs'role Hrole //. }
  iAssert (log_recs γ s'.(pstate.base) s'.(pstate.log)) as "#Hrecs''".
  { rewrite Hs'base Hs'log. iExact "Hrecs'". }
  iAssert (base_ok γ s'.(pstate.base)) as "#Hbase'".
  { rewrite Hs'base. iExact "Hbase". }
  assert (Hterms_ok' : terms_ok terms s').
  { intros t Ht. rewrite Hs'term Hs'role. by apply Hterms_ok. }
  assert (Hacks_term' : acks_term s' acks).
  { intros k Hk. rewrite Hs'term. by apply Hacks_term. }
  assert (Hfull' : full_ok s'.(pstate.base) fp ∧ plog_wf s'.(pstate.base) s'.(pstate.log) ∧
                   terms_le s' (fp ++ s'.(pstate.log))).
  { rewrite Hs'base Hs'log. split_and!; [done|done|]. rewrite -Hs'log. exact HtF'. }
  assert (Hcamps_ok' : ∀ T, is_Some (camps !! T) → uint.Z T ≤ uint.Z s'.(pstate.term)).
  { intros T HT. rewrite Hs'term. by apply Hcamps_ok. }
  iAssert (own_log_ghost γ id s')
    with "[Hterms Hacks Hcamps Hvlogs Htlog']" as "Hlg".
  { iExists γm, terms, γa, acks, fp, γc, camps, γl, vlogs.
    iFrame "Hcommit' Hcown' Hhists' Hvlogs' Hacks_ok' Hmatched' Hrecs'' Hbase'".
    iFrame "Hterms Hacks Hcamps Hvlogs Htlog' Htfrags Hafrags Hfrecs". iPureIntro. done. }
  (* the self-acknowledgement *)
  iAssert (is_leader γ id s'.(pstate.term)) as "#Hl'".
  { rewrite Hs'term. iExact "Hl". }
  iDestruct (own_log_ghost_lead_full with "Hl' Hlg") as "[(%fp' & #Hp' & #Hpf' & _) Hlg]";
    first (rewrite Hs'role //).
  iDestruct (lead_full_intro with "Hp' Hpf'") as "#HLf".
  iMod (own_log_ghost_ack _ _ _ (plast_index s') with "[] [] Hlg") as "[Hlg #Hack]".
  { iIntros ([_ Hlt]).
    assert (HLs' : plog_last_index_Z s'.(pstate.base) s'.(pstate.log) = L + Z.of_nat (length ents)).
    { rewrite Hs'log Hs'base /plog_last_index_Z length_app Hlen. rewrite /L /plog_last_index_Z. lia. }
    assert (Hpl : uint.Z (plast_index s') = L + Z.of_nat (length ents)).
    { rewrite /plast_index HLs'. word. }
    change ((s'.(pstate.term), plast_index s').1) with (s'.(pstate.term)).
    change ((s'.(pstate.term), plast_index s').2) with (plast_index s').
    iSplit; first (iPureIntro; lia).
    iExists id, s'.(pstate.base), s'.(pstate.log). iFrame "Hp'".
    iSplit; last (iExists fp'; iFrame "Hpf'").
    iPureIntro. split; [|done]. apply plog_term_at_in_range.
    split; [rewrite Hs'base; lia|rewrite HLs'; lia]. }
  { iIntros (fp2 [Hf2 Hw2]) "#Hfr2 _".
    iPoseProof "Hpf'" as (?) "(_ & #Hfr' & %Hf' & _)".
    iDestruct (full_ok_unique with "Hfr2 Hfr'") as %<-; [done|done|].
    iDestruct (lead_full_wf with "HLf") as "[[%HwL _] #HrL]".
    iApply (hist_of_agree _ _ (fp2 ++ s'.(pstate.log)) with "HrL"); [done| |done|].
    - apply plog_term_at_in_range. rewrite base0_index (full_last_index s'.(pstate.base)) //.
      rewrite /plast_index. pose proof (plog_wf_range _ _ Hw2).
      pose proof (plog_last_index_Z_nonneg s'.(pstate.base) s'.(pstate.log)). word.
    - iLeft. iExists s'.(pstate.term). iFrame "HLf". iPureIntro.
      rewrite /bnd decide_False; [lia|]. rewrite Hs'role Hrole. naive_solver. }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [-] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite psend_msgs_outbox big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /pself_ack /=. iExact "Hack".
  - rewrite psend_msgs_votes /=. iFrame "#".
  - rewrite /leader_wit psend_msgs_role psend_msgs_term /= Hrole. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_snap_stale]: back to follower of [m.from], acknowledging the
    commit index -- [step_app_stale]'s update. *)
Local Lemma own_raft_ghost_step_snap_stale γ id s m :
  m.(msg.ty) = mtype.Snap →
  m.(msg.from) ≠ id →
  s.(pstate.role) ≠ role.Leader →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs (padopt_leader s m.(msg.from))
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false s.(pstate.commit)
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hfid Hrole. iIntros "#Hm Hown". destruct_ghost.
  iAssert (⌜ m.(msg.from) ≠ W64 0 ⌝)%I as %Hfnz.
  { rewrite /is_message Hty. iDestruct "Hm" as "(_ & _ & _ & $)". }
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  iDestruct (own_log_ghost_mono γ id s (padopt_leader s m.(msg.from)) with "Hlg") as "Hlg";
    [log_mono_tac..|].
  iMod (own_log_ghost_ack _ _ _ s.(pstate.commit) with "[] [] Hlg") as "[Hlg #Hack]".
  { iIntros ([_ ?]). simpl in *. lia. }
  { iIntros (fp [Hf Hw]) "#Hfr #Hc". iApply (hist_of_commit with "[] Hc").
    - by eapply full_wf.
    - rewrite /bnd /= decide_False; [lia|]. naive_solver.
    - iApply (log_recs_full with "Hfr Hrecs"). done. }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_snap_fastfwd]: the new commit index is the snapshot's, which the
    message carries the commit fact for and the log reaches (it has the
    snapshot's last entry, which the leader's log has too). *)
Local Lemma own_raft_ghost_step_snap_fastfwd γ id s m :
  m.(msg.ty) = mtype.Snap →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) < uint.Z m.(msg.index) →
  plog_matches s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs
       (padopt_leader s m.(msg.from) <| pstate.commit := m.(msg.index) |>)
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false m.(msg.index)
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hfid Hterm Hrole Hlt Hmt. iIntros "#Hm Hown". destruct_ghost.
  iAssert ((∃ bL l fpL, lead_prefix γ m.(msg.from) m.(msg.term) bL l ∗
              ⌜ plog_term_at bL l m.(msg.index) = Some m.(msg.logterm) ⌝ ∗
              lpfull γ m.(msg.from) m.(msg.term) bL l fpL ∗
              commit_in γ (fpL ++ l) m.(msg.index) m.(msg.term)) ∗
           ⌜ m.(msg.from) ≠ W64 0 ⌝)%I
    as "((%bL & %l' & %fpL & #Hp' & %Hidx' & #Hpf' & #Hmc) & %Hfnz)".
  { iEval (rewrite /is_message Hty) in "Hm". iDestruct "Hm" as "(_ & _ & $ & $)". }
  iEval (rewrite Hterm) in "Hmc".
  iPoseProof "Hpf'" as (FL0) "(_ & _ & %HfL & _)".
  pose proof (plog_term_at_Some_range _ _ _ _ Hidx') as [HbL _].
  pose proof (plog_term_at_Some_range _ _ _ _ Hmt) as [Hb Hle]. simpl in Hb, Hle.
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  set (s1 := padopt_leader s m.(msg.from) <| pstate.commit := m.(msg.index) |>).
  iPoseProof (own_log_ghost_mono' γ id s s1 with "Hlg [] []") as "Hlg";
    [log_mono_tac..| right; simpl; lia | | |].
  { rewrite /matched_ok /=. done. }
  { iIntros (fp [Hf Hw]) "_ _". simpl.
    iApply (commit_in_agree with "Hmc"); [done|].
    rewrite (full_term_at bL fpL) //; try lia. rewrite (full_term_at s.(pstate.base) fp) //; try lia.
    rewrite Hidx'. exact Hmt. }
  iMod (own_log_ghost_ack _ _ _ m.(msg.index) with "[] [] Hlg") as "[Hlg #Hack]".
  { iIntros ([_ ?]). simpl in *. lia. }
  { iIntros (fp [Hf Hw]) "#Hfr #Hc". iApply (hist_of_commit with "[] Hc").
    - by eapply full_wf.
    - rewrite /bnd /= decide_False; [lia|]. naive_solver.
    - iApply (log_recs_full with "Hfr [Hrecs]"); [done|]. simpl. iExact "Hrecs". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_snap_restore]: the log is replaced by the snapshot -- no entries
    after the new base, so no records to keep; the compacted prefix is the
    leader's full log up to the snapshot -- and the commit index becomes
    the snapshot's, which the message carries the commit fact for.  No
    justified acknowledgement of this term is above the snapshot: the log
    would then agree with the leader at the snapshot's index
    ([ack_agree_term]), where the leader has the snapshot's last entry --
    but the rule's premise is that the log does not have it.  Histories
    move to the leader's log ([hist_replace]), which disagrees with the old
    log at the snapshot's index. *)
Local Lemma own_raft_ghost_step_snap_restore γ id s m :
  m.(msg.ty) = mtype.Snap →
  m.(msg.from) ≠ id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) < uint.Z m.(msg.index) →
  ¬ plog_matches s.(pstate.base) s.(pstate.log)
      (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs
       (padopt_leader s m.(msg.from)
          <| pstate.base := raft.entryID.mk m.(msg.logterm) m.(msg.index) |>
          <| pstate.log := [] |>
          <| pstate.commit := m.(msg.index) |>)
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false m.(msg.index)
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hfid Hterm Hrole Hlt Hnm. iIntros "#Hm Hown". destruct_ghost.
  iAssert (is_snap_meta γ m.(msg.logterm) m.(msg.index) ∗
           (∃ bL l fpL, lead_prefix γ m.(msg.from) m.(msg.term) bL l ∗
              ⌜ plog_term_at bL l m.(msg.index) = Some m.(msg.logterm) ⌝ ∗
              lpfull γ m.(msg.from) m.(msg.term) bL l fpL ∗
              commit_in γ (fpL ++ l) m.(msg.index) m.(msg.term)) ∗
           ⌜ m.(msg.from) ≠ W64 0 ⌝)%I
    as "(#Hmeta & (%bL & %l' & %fpL & #Hp' & %Hidx' & #Hpf' & #Hmc) & %Hfnz)".
  { iEval (rewrite /is_message Hty) in "Hm". iDestruct "Hm" as "(_ & $ & $ & $)". }
  iEval (rewrite Hterm) in "Hp' Hpf' Hmc".
  iDestruct (lead_full_intro with "Hp' Hpf'") as "#HLf".
  iDestruct (lead_full_wf with "HLf") as "[[%HwLf %HtLf] #HrLf]".
  iPoseProof "Hpf'" as (FL0) "(_ & _ & %HfL & _)".
  set (Lf := fpL ++ l').
  iDestruct (own_log_ghost_recs with "Hlg") as "#[%Hok Hrecs]".
  destruct Hok as (Hwf & Hbc & Hcl).
  pose proof (plog_term_at_Some_range _ _ _ _ Hidx') as [HbL _].
  set (idx := m.(msg.index)).
  assert (HLidx : plog_term_at base0 Lf idx = Some m.(msg.logterm)).
  { rewrite /Lf (full_term_at bL fpL) //. }
  set (fp' := take (Z.to_nat (uint.Z idx)) Lf).
  assert (Hfp' : full_ok (raft.entryID.mk m.(msg.logterm) idx) fp') by (by apply full_ok_take).
  assert (Hfp'j : ∀ j : w64, uint.Z j ≤ uint.Z idx →
             plog_term_at base0 (fp' ++ []) j = plog_term_at base0 Lf j).
  { intros j Hj. rewrite app_nil_r /fp' plog_term_at_take_full //. lia. }
  assert (Hfp'last : plog_last_index_Z base0 (fp' ++ []) = uint.Z idx).
  { rewrite app_nil_r. pose proof Hfp' as (Hl & _). rewrite /plog_last_index_Z base0_index. simpl in Hl. lia. }
  set (s' := padopt_leader s m.(msg.from)
               <| pstate.base := raft.entryID.mk m.(msg.logterm) m.(msg.index) |>
               <| pstate.log := [] |>
               <| pstate.commit := m.(msg.index) |>).
  assert (Hbnd' : bnd s' = uint.Z s.(pstate.term) + 1).
  { rewrite /bnd /= decide_False //. naive_solver. }
  iPoseProof (own_log_ghost_upd γ id s s'
               with "Hlg [] [] [] [Hmeta] []") as "Hlg"; [log_mono_tac..| | | | | | | | ].
  { rewrite Hbnd'. rewrite /bnd. case_decide; lia. }
  { rewrite /log_ok /plog_last_index_Z /=. split_and!; [by intros ??|lia|lia]. }
  { iIntros "!> _ %i %Hi #Ha". simpl in Hi.
    iDestruct (ack_agree_term _ _ _ _ i _ bL l' m.(msg.index) Hwf with "Hrecs Ha Hp'")
      as %Hj; [lia|lia|lia|rewrite Hidx'; by eexists|].
    exfalso. apply Hnm. rewrite /plog_matches /= Hj Hidx' //. }
  { rewrite /log_recs /=. done. }
  { rewrite /matched_ok /=. done. }
  { rewrite /base_ok /=. iRight. iExact "Hmeta". }
  { iIntros (fp (Hf & Hw & Htle)) "#Hfr #Hc".
    iExists fp'. simpl.
    iSplit; [iPureIntro; split_and!|iSplit; [|iSplit]].
    - done.
    - by intros ??.
    - intros j x Hx. split; [|done].
      rewrite app_nil_r /fp' in Hx.
      pose proof (plog_term_at_Some_range _ _ _ _ Hx) as [_ Hj].
      rewrite /plog_last_index_Z length_take base0_index in Hj.
      rewrite plog_term_at_take_full in Hx; [|lia]. by apply (HtLf j x).
    - intros Hr. exfalso. by apply Hr.
    - iApply log_recs_take. iExact "HrLf".
    - iApply (commit_in_agree with "Hmc"); [done|]. apply Hfp'j. lia.
    - iIntros "!> %t %i %Ht #Hh". rewrite Hbnd'.
      iDestruct (log_recs_full with "Hfr Hrecs") as "#HrF"; first done.
      iApply (hist_replace _ _ _ Lf t i s.(pstate.term) _ _ 1 idx idx with "HLf Hh").
      + rewrite /bnd. case_decide; lia.
      + done.
      + lia.
      + rewrite /idx. word.
      + rewrite /idx. word.
      + intros j Hj. assert (uint.Z j = 0) as Hj0 by word.
        rewrite /plog_term_at !base0_index. repeat case_decide; try lia. done.
      + intros j Hj. rewrite Hfp'j; [|lia]. split; [done|].
        apply (full_term_at_some _ _ idx); [rewrite HLidx; by eexists|lia].
      + assert (Hidxb : uint.Z s.(pstate.base).(raft.entryID.index') ≤ uint.Z idx) by (rewrite /idx; lia).
        rewrite HLidx (full_term_at s.(pstate.base) fp s.(pstate.log) idx Hf Hidxb). exact Hnm.
      + intros j Hj. apply plog_term_at_None_range. right. rewrite Hfp'last. lia. }
  iMod (own_log_ghost_ack _ _ _ m.(msg.index) with "[] [] Hlg") as "[Hlg #Hack]".
  { iIntros ([_ ?]). simpl in *. lia. }
  { iIntros (fp [Hf Hw]) "#Hfr #Hc". iApply (hist_of_commit with "[] Hc").
    - by eapply full_wf.
    - rewrite Hbnd' /s' /=. lia.
    - iApply (log_recs_full with "Hfr []"); [done|]. rewrite /log_recs /=. done. }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** *** The refinement obligation *)

Lemma own_raft_ghost_step γ (id : w64) s recv s' :
  step γ.(re_cfg) id s recv s' →
  ([∗ list] m ∈ recv, is_message γ m) -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  intros Hstep.
  induction Hstep as
    [ s
    | s0 r1 s1 r2 s2 Hst1 IH1 Hst2 IH2
    | m s Hlt Hto Hfl
    | s peers Hrole Hin Hnowrap Hperm
    | m s Hty Hto Hfrom Hterm Hcan Hutd
    | m s Hty Hto
    | m s Hty Hto Hterm Hrole
    | s mt ms Hrole Hq Hnw Hmt Hms
    | s Hrole Hnq
    | s o' Hsub
    | m s lastnewi es' Hty Hto Hfid Hterm Hrole Hcm Happ Hci
    | m s Hty Hto Hfid Hterm Hrole Hidx
    | m s hint hintterm Hty Hto Hfid Hterm Hrole Hcm Hnm
    | m s Hty Hto Hfid Hterm Hrole Hcm
    | s ms Hrole Hms
    | m s x Hty Hto Hterm Hrole Hrej Hx
    | s n Hrole Hlt Hle Htm Hq
    | s ms Hrole Hms
    | s ents Hrole Hnorm Hnw
    | m s Hty Hrole Hlead
    | m s Hty Hto Hfid Hterm Hrole Hvoters Hidin Hlt Hnm
    | m s Hty Hto Hfid Hterm Hrole Hvoters Hidin Hlt Hmt
    | m s Hty Hto Hfid Hterm Hrole Hle ].

  - (* step_refl *)
    iIntros "_ Hown". by iFrame.

  - (* step_trans *)
    iIntros "Hrecv Hown".
    iEval (rewrite big_sepL_app) in "Hrecv".
    iDestruct "Hrecv" as "[Hr1 Hr2]".
    iMod (IH1 with "Hr1 Hown") as "Hown".
    by iMod (IH2 with "Hr2 Hown") as "$".

  - (* step_higher_term: a strictly greater term, so the vote is cleared and
       the new term is fresh in the history *)
    iIntros "_ Hown". destruct_ghost.
    assert (Hne : m.(msg.term) ≠ s.(pstate.term)).
    { intros Heq. rewrite Heq in Hlt. lia. }
    pose proof Hhist as Hh; destruct Hh as [Hdom Heq].
    assert (Hhist' : vote_hist_ok voted (pbecome_follower s m.(msg.term)
                       (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))).
    { rewrite /vote_hist_ok (pbecome_follower_vote_ne _ _ _ Hne).
      split.
      - simpl. intros t Ht. specialize (Hdom t Ht). lia.
      - simpl. rewrite ?decide_True //.
        eapply (vote_hist_fresh voted s); [exact Hhist|done]. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]");
      [ idtac ..
      | rewrite /lead_ok /pbecome_follower /=; intros _;
        destruct (from_leader m.(msg.ty)); [by apply Hfl | congruence]
      | follower_votes_tac | role_ok_tac ].
    + iPureIntro. exact Hhist'.
    + by rewrite /pbecome_follower /=.
    + rewrite /pbecome_follower /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /pbecome_follower /=. done.
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_campaign: the term goes up by one, so it is fresh, and the node
       votes for itself there *)
    iIntros "_ Hown". destruct_ghost.
    iMod (own_log_ghost_campaign with "Hlg") as (kv F) "(Hlg & #Hcamp & #Hvl & #HrF & %HwF & %HlastF)";
      [done|done|].
    set (t' := word.add s.(pstate.term) (W64 1)).
    assert (Ht' : uint.Z t' = uint.Z s.(pstate.term) + 1) by (subst t'; word).
    assert (Hcterm : (pbecome_candidate id s).(pstate.term) = t') by reflexivity.
    assert (Hcvote : (pbecome_candidate id s).(pstate.vote) = id) by reflexivity.
    assert (Hfree : voted !! t' = None).
    { eapply (vote_hist_fresh voted s); [done|lia]. }
    iMod (ghost_map_insert_persist t' id Hfree with "Hvoted") as "[Hvoted #Hself]".
    iAssert (is_vote γ id t' id) as "#Hisvote".
    { iExists γv. by iFrame "#". }
    assert (Hhist' : vote_hist_ok (<[t' := id]> voted) (pbecome_candidate id s)).
    { destruct Hhist as [Hdom _]. rewrite /vote_hist_ok Hcterm Hcvote. split.
      - intros t [c Hc]. destruct (decide (t = t')) as [->|Hne]; first lia.
        assert (Hne' : t' ≠ t) by congruence.
        rewrite lookup_insert_ne // in Hc.
        unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
      - rewrite lookup_insert_eq decide_False //. }
    iAssert (vote_just γ id t' id) as "#Hvj".
    { iExists kv, F, F. iFrame "Hvl Hcamp HrF". iPureIntro. split; [done|].
      rewrite /plog_up_to_date bool_decide_eq_true. right. split; [done|lia]. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv (<[t' := id]> voted) Hname Hidnz
             with "Hvoted [] [] [] [] [] [Hlg] [%] [%] [] [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | idtac | idtac ].
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist'); reflexivity.
    + rewrite big_sepM_insert //. by iFrame "#".
    + rewrite /psend_msgs /pbecome_candidate /=.
      rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_cons. iSplitR.
      * by iApply is_message_grant.
      * rewrite big_sepL_fmap. iApply big_sepL_intro.
        iIntros "!> %k %x %Hk". rewrite /is_message /pvote_req /=.
        iExists F. iFrame "Hcamp". iPureIntro. rewrite HlastF.
        by destruct (plog_last s.(pstate.base) s.(pstate.log)).
    + rewrite /psend_msgs /pbecome_candidate /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /psend_msgs /pbecome_candidate /=. done.
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
    + rewrite big_sepM_insert //. by iFrame "#".
    + rewrite /role_ok /psend_msgs /pbecome_candidate /=. done.

  - (* step_grant_vote: either the node has already voted this way, or the
       current term is free in the history -- then the vote records the
       voter's log, which the candidate's campaign log (the request carries
       it) is at least as up to date as *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]". destruct_ghost.
    iAssert (∃ Fc, is_camp γ m.(msg.from) m.(msg.term) Fc ∗
               ⌜ plog_last base0 Fc = raft.entryID.mk m.(msg.logterm) m.(msg.index) ⌝)%I
      as (Fc) "[#Hcamp %HFc]".
    { rewrite /is_message Hty. iExact "Hm". }
    iEval (rewrite Hterm) in "Hcamp".
    iAssert (|==> ∃ voted', ghost_map_auth γv 1 voted' ∗
                  ⌜ vote_hist_ok voted' (s <| pstate.vote := m.(msg.from) |>) ⌝ ∗
                  ([∗ map] t ↦ c ∈ voted', is_vote γ id t c) ∗
                  ([∗ map] t ↦ c ∈ voted', vote_just γ id t c) ∗
                  is_vote γ id s.(pstate.term) m.(msg.from) ∗ own_log_ghost γ id s)%I
      with "[Hvoted Hlg]" as ">(%voted' & Hvoted & %Hhist' & #Hfrags' & #Hvrecs' & #Hgrant & Hlg)".
    { destruct Hcan as [Hsame | [Hnovote Hnolead]].
      - (* already voted for this candidate *)
        destruct Hhist as [Hdom Heq].
        assert (Hvnz : s.(pstate.vote) ≠ W64 0) by (rewrite Hsame; exact Hfrom).
        assert (Hlook : voted !! s.(pstate.term) = Some m.(msg.from)).
        { rewrite Heq decide_False //. by rewrite Hsame. }
        iExists voted. iFrame "Hvoted Hfrags Hvrecs Hlg".
        iDestruct (big_sepM_lookup _ _ _ _ Hlook with "Hfrags") as "#Hone".
        iFrame "Hone". iPureIntro.
        split; [exact Hdom|]. simpl. rewrite -Hsame. exact Heq.
      - (* first vote of this term: no leader, so a follower *)
        assert (Hfree : voted !! s.(pstate.term) = None).
        { destruct Hhist as [_ Heq]. rewrite Heq decide_True //. }
        assert (Hbnd : bnd s = uint.Z s.(pstate.term)).
        { rewrite /bnd decide_True //. split; [done|]. intros Hr.
          destruct Hrok as [Hv _]. apply Hidnz. rewrite -Hnovote. symmetry. apply Hv. congruence. }
        iMod (own_log_ghost_vote with "Hlg") as (kv Fv) "(Hlg & #Hvl & #HrFv & %HwFv & %Hutd')"; [done|].
        iMod (ghost_map_insert_persist s.(pstate.term) m.(msg.from) Hfree
               with "Hvoted") as "[Hvoted #Hnew]".
        iAssert (is_vote γ id s.(pstate.term) m.(msg.from)) as "#Hisvote".
        { iExists γv. by iFrame "#". }
        iModIntro. iExists (<[s.(pstate.term) := m.(msg.from)]> voted).
        iFrame "Hvoted Hisvote Hlg".
        iSplitR.
        + iPureIntro. destruct Hhist as [Hdom _]. split.
          * simpl. intros t [c Hc]. destruct (decide (t = s.(pstate.term)))
              as [->|Hne]; first lia.
            assert (Hne' : s.(pstate.term) ≠ t) by congruence.
            rewrite lookup_insert_ne // in Hc.
            unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
          * simpl. rewrite lookup_insert_eq decide_False //.
        + iSplit; [rewrite big_sepM_insert //; by iFrame "#"|].
          rewrite big_sepM_insert //. iSplitR; [|iExact "Hvrecs"].
          iExists kv, Fv, Fc. iSplit; first iExact "Hvl". iSplit; first iExact "Hcamp".
          iSplit; first iExact "HrFv". iPureIntro. split; [done|].
          rewrite Hutd' HFc. exact Hutd. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted' Hname Hidnz
             with "Hvoted [] Hfrags' [] [] [] [Hlg] [%] [%] Hvrecs' [%]");
      [ idtac .. | lead_ok_tac | follower_votes_tac
      | (destruct Hrok as [Hv Hc]; rewrite /role_ok /psend_msgs /=; split; [|done]; intros Hr;
         destruct Hcan as [Hs|[Hn _]];
         [rewrite -Hs; by apply Hv|exfalso; apply Hidnz; rewrite -Hn; symmetry; by apply Hv]) ].
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist'); reflexivity.
    + rewrite /psend_msgs /=. rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_singleton. by iApply is_message_grant.
    + rewrite /psend_msgs /=. iFrame "#".
    + rewrite /leader_wit /psend_msgs /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_reject_vote: a rejection carries nothing *)
    iIntros "_ Hown". destruct_ghost.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + rewrite /psend_msgs /=. rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_singleton. by iApply is_message_reject.
    + rewrite /psend_msgs /=. iFrame "#".
    + rewrite /leader_wit /psend_msgs /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_record_vote: a granting response is backed by the voter's vote *)
    iIntros "Hrecv Hown".
    iDestruct "Hrecv" as "[#Hm _]".
    destruct_ghost.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + iFrame "#".
    + simpl. iApply big_sepS_intro. iIntros "!> %v %Hv".
      apply elem_of_granted_record_vote in Hv as [Hv | [-> Hb]].
      * by iApply (big_sepS_elem_of _ _ _ Hv with "Htally").
      * assert (Hrej : m.(msg.reject) = false)
          by (destruct (m.(msg.reject)); [discriminate Hb|reflexivity]).
        rewrite -Hterm -Hto.
        iApply (is_message_grant_inv γ m Hty Hrej with "Hm").
    + rewrite /leader_wit /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_win *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_win with "Hown") as "$".

  - (* step_lose: back to follower in the same term, so the vote stands *)
    iIntros "_ Hown". destruct_ghost.
    assert (Hhist' : vote_hist_ok voted
                       (pbecome_follower s s.(pstate.term) (W64 0))).
    { destruct Hhist as [Hdom Heq].
      rewrite /vote_hist_ok pbecome_follower_vote_same.
      split; simpl; [done|exact Heq]. }
    pose proof (proj2 Hrok Hrole) as Hlead0.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
    + iPureIntro. exact Hhist'.
    + by rewrite /pbecome_follower /=.
    + rewrite /pbecome_follower /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /pbecome_follower /=. done.
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_drain: the messages kept are messages that were there *)
    iIntros "_ Hown". destruct_ghost.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg] [%] [%] Hvrecs [%]"); [ idtac .. | lead_ok_tac | follower_votes_tac | role_ok_tac ].
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + simpl. iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      iApply (big_sepL_elem_of with "Hout").
      eapply elem_of_submseteq; [by eapply list_elem_of_lookup_2|done].
    + simpl. iFrame "#".
    + rewrite /leader_wit /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_app_accept *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_app_accept with "Hm Hown") as "$".

  - (* step_app_stale *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_app_stale with "Hm Hown") as "$".

  - (* step_app_reject *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_app_reject with "Hm Hown") as "$".

  - (* step_heartbeat *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_heartbeat with "Hm Hown") as "$".

  - (* step_beat *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_beat with "Hown") as "$".

  - (* step_app_resp *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_app_resp with "Hm Hown") as "$".

  - (* step_commit *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_commit with "Hown") as "$".

  - (* step_send_apps *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_send_apps with "Hown") as "$".

  - (* step_propose *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_propose with "Hown") as "$".

  - (* step_prop_forward *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_prop_forward with "Hown") as "$".

  - (* step_snap_restore *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_snap_restore with "Hm Hown") as "$".

  - (* step_snap_fastfwd *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_snap_fastfwd with "Hm Hown") as "$".

  - (* step_snap_stale *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_snap_stale with "Hm Hown") as "$".
Qed.

(** *** Protocol facts the code needs

    Each is a [Panicf] in the replication code that is dead only by protocol
    reasoning (notes/raft-replication-model.md, "Protocol facts the code
    needs").  A callee's spec takes the fact as a premise; [Step] derives it
    here, from the node's ghost state and the incoming message.

    **The message may be of a higher term** (since 2026-10-02): [Step]
    holds the ghost state at the state *before* its term preamble, and a
    message from a later term makes the node step down first
    ([becomeFollower] keeps the log and the commit index), so each lemma is
    stated for [ps.term ≤ m.term] rather than equality.  A stale message
    ([m.term < ps.term]) is dropped by the preamble and needs none of them,
    except [app_recv_wf], which holds of any [App] ([is_message] carries
    it).  All four are proved (the last two since 2026-10-02, from the
    acknowledgement invariant [acks_ok] and from arithmetic). *)

(** [handleHeartbeat]'s [commitTo(m.Commit)] panics if [lastIndex() <
    m.Commit].  It does not: the leader sends [Commit ≤ pr.Match], and
    [is_message] carries the receiver's acknowledgement of [pr.Match] in
    [m.term].  The receiver acknowledges only at its own term
    ([acks_term]), so for a message of a higher term [pr.Match] is [0];
    at its own term (where it is not leader -- the role premise) the
    acknowledgement is at most the commit index or justified by its log
    ([acks_ok], [ack_agree]), and either way within it ([log_ok]).  [Step]
    holds the ghost state before its term preamble: hence [≤]. *)
Lemma heartbeat_commit_le_last γ id ps m :
  m.(msg.ty) = mtype.Heartbeat →
  m.(msg.to) = id →
  uint.Z ps.(pstate.term) ≤ uint.Z m.(msg.term) →
  (m.(msg.term) = ps.(pstate.term) → ps.(pstate.role) ≠ role.Leader) →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ uint.Z m.(msg.commit) ≤ plog_last_index_Z ps.(pstate.base) ps.(pstate.log) ⌝.
Proof.
  iIntros (Hty Hto Hle Hrole) "Hown #Hm".
  iEval (rewrite /is_message Hty) in "Hm".
  iDestruct "Hm" as "(_ & _ & (%i & %Hci & Hack) & _)".
  iDestruct "Hown" as (γv voted) "(_ & _ & _ & _ & _ & _ & _ & _ & Hlg & _)".
  iDestruct "Hlg" as (γm terms γa acks fp γc camps γl vlogs) "Hlg". iNamed "Hlg".
  destruct Hlog_ok as (_ & _ & Hcl).
  pose proof (plog_last_index_Z_nonneg ps.(pstate.base) ps.(pstate.log)).
  iDestruct "Hack" as "[%H0 | (%γa' & %Hγa' & Hfrag)]".
  { iPureIntro. lia. }
  rewrite Hto Haname in Hγa'. injection Hγa' as <-.
  iDestruct (ghost_map_lookup with "Hacks Hfrag") as %Hk.
  pose proof (Hacks_term _ ltac:(by eexists)) as Hkt. simpl in Hkt.
  assert (Heq : m.(msg.term) = ps.(pstate.term)) by (apply word.unsigned_inj; lia).
  specialize (Hrole Heq).
  rewrite /acks_ok. destruct (ps.(pstate.role)) eqn:Hr; [| |congruence].
  all: iDestruct (big_sepM_lookup with "Hacks_ok") as "Hk"; first exact Hk.
  all: destruct (decide (uint.Z ps.(pstate.commit) < uint.Z i)) as [Hlt|Hge];
         [|iPureIntro; lia].
  all: iDestruct ("Hk" $! (conj Heq Hlt)) as "[%Hil _]".
  all: simpl in Hil; iPureIntro; lia.
Qed.

(** What [raftLog.maybeAppend] needs of a received [App]'s batch: carried
    by the message ([app_payload_ok]).  No premise on the terms: it is a
    fact of the message alone (until 2026-10-02 it was stated for
    [m.term = ps.term]). *)
Lemma app_recv_wf γ id ps m :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ plog_wf (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries) ∧
    uint.Z m.(msg.index) + Z.of_nat (length m.(msg.entries)) + 1 < 2 ^ 64 ∧
    Forall (λ e, e.(raftpb.Entry.Type') = W32 0) m.(msg.entries) ⌝.
Proof.
  iIntros (Hty _) "_ Hm". rewrite /is_message Hty.
  iDestruct "Hm" as "(%Hpay & _)". done.
Qed.

(** [maybeAppend]'s [commitTo(min(committed, lastnewi))] panics if the log
    ends before it: it never does ([plog_maybe_append_last], from the
    batch's [app_payload_ok]). *)
Lemma app_commit_le_lastnewi γ id ps m lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  uint.Z ps.(pstate.term) ≤ uint.Z m.(msg.term) →
  plog_maybe_append ps.(pstate.base) ps.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ uint.Z lastnewi ≤ plog_last_index_Z ps.(pstate.base) es' ⌝.
Proof.
  iIntros (Hty Hto _ Happ) "Hown #Hm".
  iDestruct (app_recv_wf with "Hown Hm") as %(Hwf & Hnw & _); [done..|].
  iPureIntro. eapply plog_maybe_append_last; [exact Hwf| |exact Happ]. exact Hnw.
Qed.

(** [maybeAppend] panics if the first conflicting index is at or below the
    commit index ([ci ≤ l.committed]).  Under [maybeAppend]'s caller's
    premise [committed ≤ m.Index] that is arithmetic: a conflict is the
    index of one of the batch's entries, which are at [m.Index + 1] and
    above ([app_payload_ok]).  (Until 2026-10-02 this was admitted as a
    consequence of Leader Completeness; the premise makes it local.  The
    term premise is not needed.) *)
Lemma app_no_conflict_below_commit γ id ps m :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  uint.Z ps.(pstate.term) ≤ uint.Z m.(msg.term) →
  uint.Z ps.(pstate.commit) ≤ uint.Z m.(msg.index) →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ plog_matches ps.(pstate.base) ps.(pstate.log)
      (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
    plog_find_conflict ps.(pstate.base) ps.(pstate.log) m.(msg.entries) = W64 0 ∨
    uint.Z ps.(pstate.commit)
    < uint.Z (plog_find_conflict ps.(pstate.base) ps.(pstate.log) m.(msg.entries)) ⌝.
Proof.
  iIntros (Hty _ _ Hcm) "_ Hm". iEval (rewrite /is_message Hty) in "Hm".
  iDestruct "Hm" as "(%Hpay & _)". iPureIntro. intros _.
  destruct Hpay as (Hwf & Hnw & _).
  destruct (decide (plog_find_conflict ps.(pstate.base) ps.(pstate.log) m.(msg.entries) = W64 0))
    as [|Hne]; [by left|right].
  destruct (plog_find_conflict_some _ _ _ Hne) as (d & e & Hd & He & _ & _).
  specialize (Hwf _ _ Hd). simpl in Hwf. rewrite -He. lia.
Qed.

(** *** Replication safety

    The three properties replication is for, as entailments between the
    ghost states of nodes.  Log Matching is proved (2026-10-02).  Leader
    Completeness and State Machine Safety are ADMITTED, and **cannot be
    proved as stated**, from the ghost state of two nodes: see
    [leader_completeness]'s comment for why and for what a proof needs. *)

(** A node's log and its records. *)
Lemma own_raft_ghost_log γ id s :
  own_raft_ghost γ id s -∗ ⌜ log_ok s ⌝ ∗ log_recs γ s.(pstate.base) s.(pstate.log).
Proof.
  iIntros "Hown". iDestruct "Hown" as (γv voted) "(_ & _ & _ & _ & _ & _ & _ & _ & Hlg & _)".
  iApply (own_log_ghost_recs with "Hlg").
Qed.

(** Log Matching: two logs that have the same term at an index agree on
    every entry up to it (above both bases).  Proved since 2026-10-02 from
    the two logs' records alone ([log_recs_agree], [plog_match_down]):
    entries at one (term, index) are one entry with one predecessor term,
    because the term log of that term's (unique) leader says so. *)
Lemma log_matching γ id1 id2 s1 s2 (i t : w64) :
  plog_term_at s1.(pstate.base) s1.(pstate.log) i = Some t →
  plog_term_at s2.(pstate.base) s2.(pstate.log) i = Some t →
  own_raft_ghost γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗
  ⌜ ∀ j : w64, uint.Z j ≤ uint.Z i →
      uint.Z s1.(pstate.base).(raft.entryID.index') < uint.Z j →
      uint.Z s2.(pstate.base).(raft.entryID.index') < uint.Z j →
      plog_entry_at s1.(pstate.base) s1.(pstate.log) j =
      plog_entry_at s2.(pstate.base) s2.(pstate.log) j ⌝.
Proof.
  iIntros (H1 H2) "H1 H2".
  iDestruct (own_raft_ghost_log with "H1") as "[%Hok1 #Hr1]".
  iDestruct (own_raft_ghost_log with "H2") as "[%Hok2 #Hr2]".
  destruct Hok1 as (Hwf1 & _ & _). destruct Hok2 as (Hwf2 & _ & _).
  iDestruct (log_recs_agree with "Hr1 Hr2") as %HRA.
  iPureIntro. intros j Hji Hb1 Hb2.
  assert (Hj : plog_term_at s1.(pstate.base) s1.(pstate.log) j =
               plog_term_at s2.(pstate.base) s2.(pstate.log) j).
  { apply (plog_match_down _ _ _ _ i Hwf1 Hwf2 HRA); [rewrite H1; by eexists|by rewrite H1 H2|lia..]. }
  pose proof (plog_term_at_Some_range _ _ _ _ H1) as [_ Hl1].
  destruct (plog_term_at_in_range s1.(pstate.base) s1.(pstate.log) j ltac:(lia)) as [tj Htj].
  destruct (plog_term_at_Some_entry _ _ _ _ Hwf1 Htj Hb1) as (e1 & He1 & Hi1 & Ht1).
  rewrite Hj in Htj.
  destruct (plog_term_at_Some_entry _ _ _ _ Hwf2 Htj Hb2) as (e2 & He2 & Hi2 & Ht2).
  rewrite !plog_entry_at_lookup //. rewrite He1 He2.
  pose proof (word.unsigned_range j).
  destruct (HRA _ _ _ _ He1 He2 ltac:(lia) ltac:(lia) ltac:(congruence) ltac:(congruence))
    as [-> _].
  done.
Qed.

(** Leader Completeness: an entry another node has committed, at a term no
    later than the leader's, is in the leader's log.  Informal argument
    (Raft §5.4.3): it was acknowledged by a quorum [Q] in some term [tc];
    every leader of a later term [T] was elected by a quorum [V]; [Q] and [V]
    meet in a voter [x] whose log had the entry when it voted in [T] (by
    induction on [T]: the leaders between [tc] and [T] had it, so their
    [App]s never cut [x]'s log below it), and the [isUpToDate] check
    ([step_grant_vote]'s premise) then puts the entry in the candidate's
    log, by Log Matching against the candidate's last entry.

    ADMITTED, and **not provable as stated** (2026-10-02).  The statement
    holds the ghost state of two nodes only, and quantifies over [γ]; the
    argument's middle step is about a *third* node [x] -- that its vote in
    [T] came after, and agreed with, its acknowledgement in [tc] -- and
    [x]'s votes and acknowledgements are fragments of [x]'s own maps, which
    nothing outside [x]'s [own_raft_ghost] constrains.  Counter-model: three
    voters; node 2 has [commit = i] backed by [is_committed i] from
    acknowledgements of nodes 2 and 3 in term 1; node 1 leads term 2 by
    the votes of nodes 1 and 3 and lacks the entry; node 3's ghost maps
    (held by nobody) contain both the acknowledgement and the vote.  Every
    fact the two given [own_raft_ghost]s hold is consistent with that.
    (Log Matching escapes this: it rests only on agreement of fragments,
    which no third party can break.)

    What a proof needs, precisely:
    (1) the statement over the whole cluster -- [own_raft_ghost] of every
        voter, or an Iris invariant holding them (the protocol's global
        state); with node-local ghost state there is no other way to know
        a third node behaved;
    (2) a per-node *history* invariant, which [own_raft_ghost] lacks: for
        every vote [(T ↦ c)] a node cast, its last entry id at that moment
        (so that [step_grant_vote]'s [plog_up_to_date] premise bounds [c]'s
        last id, which [c]'s log at its win -- [is_term_log]'s [l0] --
        reaches), and for every acknowledgement [(tc, i')] it made before,
        that its log at vote time still agreed with the leader of [tc] up
        to the part every leader between [tc] and [T] shares.  Today the
        justification of an acknowledgement ([acks_ok]) is kept only
        within its own term, which is all [heartbeat_commit_le_last]
        needs;
    (3) [is_committed] naming *which* entries are committed (the
        committing leader's [lead_prefix] up to [i], with [i]'s entry of
        the leader's term -- [step_commit]'s premise), so that a node's
        log up to its commit index can be said to agree with it; and the
        induction on [T] of the informal argument over those facts. *)
Lemma leader_completeness γ id1 id2 s1 s2 (i : w64) e :
  s1.(pstate.role) = role.Leader →
  uint.Z s2.(pstate.term) ≤ uint.Z s1.(pstate.term) →
  uint.Z i ≤ uint.Z s2.(pstate.commit) →
  plog_entry_at s2.(pstate.base) s2.(pstate.log) i = Some e →
  uint.Z s1.(pstate.base).(raft.entryID.index') < uint.Z i →
  own_raft_ghost γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗
  ⌜ plog_entry_at s1.(pstate.base) s1.(pstate.log) i = Some e ⌝.
Proof.
Admitted.

(** State Machine Safety: two nodes agree on every index both have
    committed.  Informal argument: Log Matching plus Leader Completeness,
    as in the Raft paper (§5.4.3): both entries are the committing
    leaders' entries at [i], and the later of the two leaders has the
    earlier one's ([leader_completeness]).  ADMITTED, for
    [leader_completeness]'s reason, and not reducible to that lemma as
    stated: the two committing leaders are third nodes, whose
    [own_raft_ghost] the statement does not hold.  With (1)-(3) of
    [leader_completeness]'s comment it is a corollary of it and
    [log_matching]. *)
Lemma state_machine_safety γ id1 id2 s1 s2 (i : w64) :
  uint.Z i ≤ uint.Z s1.(pstate.commit) →
  uint.Z i ≤ uint.Z s2.(pstate.commit) →
  uint.Z s1.(pstate.base).(raft.entryID.index') < uint.Z i →
  uint.Z s2.(pstate.base).(raft.entryID.index') < uint.Z i →
  own_raft_ghost γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗
  ⌜ plog_entry_at s1.(pstate.base) s1.(pstate.log) i =
    plog_entry_at s2.(pstate.base) s2.(pstate.log) i ⌝.
Proof.
Admitted.

(** *** Allocation

    Nothing above says the ghost state is inhabited, and an empty
    [own_raft_ghost] would make every lemma here true and useless.  This is
    what rules that out: a fresh ghost state for any set of nodes, each in the
    initial protocol state -- an empty log. *)

Definition init_pstate : pstate.t :=
  {| pstate.term := W64 0; pstate.vote := W64 0; pstate.lead := W64 0;
     pstate.role := role.Follower; pstate.votes := ∅; pstate.outbox := [];
     pstate.base := raft.entryID.mk (W64 0) (W64 0); pstate.log := [];
     pstate.commit := W64 0; pstate.matched := ∅ |}.

Local Lemma alloc_maps {K V} `{Countable K} (ids : gset w64) :
  ⊢ |==> ∃ (names : gmap w64 gname),
      [∗ set] x ∈ ids, ∃ γx, ⌜ names !! x = Some γx ⌝ ∗
                             ghost_map_auth γx 1 (∅ : gmap K V).
Proof.
  induction ids as [|x ids Hx IH] using set_ind_L.
  - iModIntro. iExists ∅. rewrite big_sepS_empty. done.
  - iMod IH as (names) "Hm".
    iMod (ghost_map_alloc_empty (K:=K) (V:=V)) as (γx) "Hauth".
    iModIntro. iExists (<[x := γx]> names).
    rewrite big_sepS_insert //. iSplitL "Hauth".
    + iExists γx. rewrite lookup_insert_eq. by iFrame.
    + iApply (big_sepS_impl with "Hm"). iIntros "!> %y %Hy (%γy & %Hγy & Ha)".
      iExists γy. iFrame "Ha". iPureIntro.
      rewrite lookup_insert_ne //. intros ->. done.
Qed.

Lemma own_raft_ghost_alloc (cfg : gset w64) (ids : gset w64) :
  W64 0 ∉ ids →
  ⊢ |==> ∃ γ, ⌜ γ.(re_cfg) = cfg ⌝ ∗
      [∗ set] id ∈ ids, own_raft_ghost γ id init_pstate.
Proof.
  iIntros (Hnz).
  iMod (alloc_maps (K:=w64) (V:=w64) ids) as (nv) "Hv".
  iMod (alloc_maps (K:=w64) (V:=term_rec) ids) as (nt) "Ht".
  iMod (alloc_maps (K:=w64 * w64) (V:=unit) ids) as (na) "Ha".
  iModIntro. iExists {| re_cfg := cfg; re_votes := nv; re_terms := nt; re_acks := na |}.
  iSplit; first done.
  iCombine "Hv Ht Ha" as "H". rewrite -!big_sepS_sep.
  iApply (big_sepS_impl with "H").
  iIntros "!> %id %Hid ((%γv & %Hγv & Hav) & (%γm & %Hγm & Hat) & (%γa & %Hγa & Haa))".
  iExists γv, ∅.
  iSplit; first done.
  iSplit.
  { iPureIntro. intros ->. by apply Hnz. }
  iFrame "Hav".
  iSplit.
  { iPureIntro. split; [by intros t []|]. rewrite lookup_empty //. }
  rewrite big_sepM_empty big_sepL_nil granted_empty big_sepS_empty.
  rewrite /leader_wit /=.
  iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
  iSplitL "Hat Haa"; last first.
  { iPureIntro. split.
    - rewrite /lead_ok /=. intros _ Heq. apply Hnz. by rewrite Heq.
    - rewrite /follower_votes_ok /=. done. }
  iExists γm, ∅, γa, ∅. iFrame "Hat Haa".
  assert (terms_ok ∅ init_pstate) by (by intros t []).
  assert (acks_term init_pstate ∅) by (intros k [? Hk]; by rewrite lookup_empty in Hk).
  assert (log_ok init_pstate)
    by (rewrite /log_ok /plog_last_index_Z /=; split_and!; [by intros ??|lia|lia]).
  iFrame "%".
  rewrite /lead_log_own /matched_ok /acks_ok /log_recs /= !big_sepM_empty.
  repeat iSplit; try done.
  - iApply is_committed_0.
  - iLeft. done.
Qed.

End ghost.

(** ** Derived conveniences used by [election.v] *)

Section lemmas.
Context `{!invGS Σ, !allG Σ}.
Implicit Type γ : raft_election_names.

(** Taking a step that consumes a single known message. *)
Lemma own_raft_ghost_step_1 γ id s m s' :
  step γ.(re_cfg) id s [m] s' →
  is_message γ m -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "#Hm Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hown") as "$".
  { by iFrame "#". }
  done.
Qed.

(** Taking a step that consumes nothing. *)
Lemma own_raft_ghost_step_0 γ id s s' :
  step γ.(re_cfg) id s [] s' →
  own_raft_ghost γ id s ={⊤}=∗ own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hown") as "$".
  { done. }
  done.
Qed.

End lemmas.
