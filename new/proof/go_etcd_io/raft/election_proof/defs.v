(** * Shared vocabulary for the election proof *)

Require Export New.proof.go_etcd_io.raft.v3_proof.base.
Require Export New.proof.go_etcd_io.raft.election_proof.protocol.

(** Discharge a goal [¬ (W32 a = W32 b)] for distinct literals. *)
Ltac w32_ne :=
  intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.

(** Introduce the binders every [wp_<fn>_body] opens with.  The one place this
    list is written; see notes/gotchas.md. *)
Ltac intros_ambient :=
  intros ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** ** Message-type constants, as Rocq values

    [raftpb.MessageType] is a [w32]; the Goose constants are opaque [val]s,
    so we name the underlying numbers. *)
Definition MsgHup : w32 := W32 0.
Definition MsgApp : w32 := W32 3.
Definition MsgAppResp : w32 := W32 4.
Definition MsgVote : w32 := W32 5.
Definition MsgVoteResp : w32 := W32 6.
Definition MsgSnap : w32 := W32 7.
Definition MsgHeartbeat : w32 := W32 8.
Definition MsgPreVote : w32 := W32 17.
Definition MsgPreVoteResp : w32 := W32 18.
Definition MsgStorageAppendResp : w32 := W32 20.

Definition StateFollower : w64 := W64 0.
Definition StateCandidate : w64 := W64 1.
Definition StateLeader : w64 := W64 2.

Definition campaignElection : raft.CampaignType.t := "CampaignElection"%go.
Definition campaignPreElection : raft.CampaignType.t := "CampaignPreElection"%go.
Definition campaignTransfer : raft.CampaignType.t := "CampaignTransfer"%go.

Definition VotePending : w8 := W8 1.
Definition VoteLost : w8 := W8 2.
Definition VoteWon : w8 := W8 3.

Definition state_w64 (ro : role.t) : w64 :=
  match ro with
  | role.Follower => StateFollower
  | role.Candidate => StateCandidate
  | role.Leader => StateLeader
  end.

(** ** Abstraction of physical messages

    Only election-related message types have an abstraction. *)
Definition mtype_of (t : w32) : option mtype.t :=
  if decide (t = MsgVote) then Some mtype.Vote
  else if decide (t = MsgVoteResp) then Some mtype.VoteResp
  else if decide (t = MsgApp) then Some mtype.App
  else if decide (t = MsgHeartbeat) then Some mtype.Heartbeat
  else None.

Lemma mtype_of_MsgVote : mtype_of MsgVote = Some mtype.Vote.
Proof. rewrite /mtype_of. case_decide as H1; [done|congruence]. Qed.

Lemma mtype_of_MsgVoteResp : mtype_of MsgVoteResp = Some mtype.VoteResp.
Proof.
  rewrite /mtype_of. case_decide as H1.
  { exfalso. rewrite /MsgVoteResp /MsgVote in H1. word. }
  case_decide as H2; [done|congruence].
Qed.

Definition abs_msg (ty : mtype.t) (m : raftpb.Message.t) : msg.t :=
  msg.mk ty m.(raftpb.Message.From') m.(raftpb.Message.To')
            m.(raftpb.Message.Term') m.(raftpb.Message.Reject').

(** The partial abstraction of a physical message: [None] for the message
    types the election model does not describe.  [MsgAppResp] is the one that
    matters — [appendEntry] queues one, so a total abstraction would make the
    abstract outbox undefined exactly where [becomeLeader] needs it. *)
Definition abs_msg_opt (m : raftpb.Message.t) : option msg.t :=
  ty ← mtype_of m.(raftpb.Message.Type'); Some (abs_msg ty m).

Lemma abs_msg_opt_Some ty m :
  mtype_of m.(raftpb.Message.Type') = Some ty → abs_msg_opt m = Some (abs_msg ty m).
Proof. rewrite /abs_msg_opt => ->. done. Qed.

(** What [step_win] demands of a winner's broadcast: any list of [App]
    messages from [id] at the given term, possibly empty.  Lives here rather
    than in [step_lemmas.v] because [inv_raft_phys.v]'s [bcastAppend] axiom
    needs it, and it does not mention [cfg]. *)
Definition app_sends (id : w64) (term : w64) (ms : list msg.t) : Prop :=
  Forall (λ m, m.(msg.ty) = mtype.App ∧ m.(msg.from) = id ∧
               m.(msg.term) = term) ms.

(** The abstract outbox of the two physical queues, together. *)
Definition abs_outbox (msgs msgsAA : list raftpb.Message.t) : list msg.t :=
  omap abs_msg_opt msgs ++ omap abs_msg_opt msgsAA.

(** [send] appends to one queue or the other depending on the message type.
    The abstract outbox grows at the end either way — but only up to
    permutation, which is why [own_raft_phys] relates the two with [≡ₚ]. *)
Lemma abs_outbox_snoc_msgs (msgs msgsAA : list raftpb.Message.t) m ty :
  mtype_of m.(raftpb.Message.Type') = Some ty →
  abs_outbox (msgs ++ [m]) msgsAA ≡ₚ abs_outbox msgs msgsAA ++ [abs_msg ty m].
Proof.
  intros Hty. rewrite /abs_outbox omap_app /=.
  rewrite (abs_msg_opt_Some ty) //= -!assoc.
  apply Permutation_app_head, Permutation_app_comm.
Qed.

Lemma abs_outbox_snoc_msgsAA (msgs msgsAA : list raftpb.Message.t) m ty :
  mtype_of m.(raftpb.Message.Type') = Some ty →
  abs_outbox msgs (msgsAA ++ [m]) ≡ₚ abs_outbox msgs msgsAA ++ [abs_msg ty m].
Proof.
  intros Hty. rewrite /abs_outbox omap_app /=.
  rewrite (abs_msg_opt_Some ty) //= assoc //.
Qed.

(** A message the model does not describe leaves the abstract outbox alone. *)
Lemma abs_outbox_snoc_msgsAA_None (msgs msgsAA : list raftpb.Message.t) m :
  mtype_of m.(raftpb.Message.Type') = None →
  abs_outbox msgs (msgsAA ++ [m]) = abs_outbox msgs msgsAA.
Proof.
  intros Hty. rewrite /abs_outbox omap_app /= /abs_msg_opt Hty /=.
  by rewrite app_nil_r.
Qed.

End proof.

(** The abstract state of a [raftLog]: what every [raftLog] spec is stated
    at.

    - [prev], [sents], [uents]: the entry list, as described above.
    - [committed], [applied]: [l.committed] and [l.applied].  Nothing on the
      election path writes them; they are in the state because
      [hasUnappliedConfChanges] and [maybeSendAppend] read them and a spec
      has to be able to say what was read.

    Every field is physical.  Until 2026-09-29 there was a sixth, [page]:
    a slice [raftLog.slice] had handed out while sharing memory with the
    log, on loan, with a wand back in [own_raftLog].  It went when the log
    started holding its entries read-only ([↦*□], [inv_raftlog.v]): a
    slice [slice] returns is then the caller's for good, and there is no
    loan to record.

    (Until 2026-09-23 the log had three shapes: [own_raftLog_at l prev sents
    uents], the existential [own_raftLog l], and the "page out" shape that
    [slice]/[entries] returned as [l ↦ lv ∗ s ↦*{dq} es ∗ (l ↦ lv -∗ s ↦*{dq}
    es -∗ own_raftLog_at …)].  notes/decisions.md, "One predicate per
    object".) *)
Module logstate.
Record t :=
  mk {
      prev : raft.entryID.t;
      sents : list raftpb.Entry.t;
      uents : list raftpb.Entry.t;
      committed : w64;
      applied : w64;
    }.
#[global] Instance settable : Settable t :=
  settable! mk <prev; sents; uents; committed; applied>.
End logstate.

(** After [destruct ls as [prev sents uents …]], reduce the projections the
    specs are written with.  Restricted to the five projections: a plain
    [simpl in *] near a struct points-to can run for minutes
    (notes/gotchas.md). *)
Ltac logstate_simpl :=
  cbn [logstate.prev logstate.sents logstate.uents logstate.committed
       logstate.applied] in *.

(** ** Physical transitions of the log

    [log_last ls] is [lastIndex()] of a log at [ls], as a [w64]; the
    [raftLog] specs return it as a [Z] equation, and [own_raftLog]'s
    [Hnowrap] says the [W64] does not wrap. *)
Definition log_last (ls : logstate.t) : w64 :=
  W64 (uint.Z ls.(logstate.prev).(raft.entryID.index')
       + Z.of_nat (length ls.(logstate.sents))
       + Z.of_nat (length ls.(logstate.uents))).

(** [raftLog.append] at the end of the log: the batch joins the unstable
    suffix ([spec_raftLog__append.v]). *)
Definition log_append (ls : logstate.t) (ents : list raftpb.Entry.t) : logstate.t :=
  ls <| logstate.uents := ls.(logstate.uents) ++ ents |>.

(** [appendEntry]'s stamping loop: [es[k].Term = r.Term] and
    [es[k].Index = li+1+k]; nothing else about an entry changes, which is
    what keeps [Type = EntryNormal] true of the appended entries. *)
Definition stamp (tm li : w64) (k : nat) (e : raftpb.Entry.t) : raftpb.Entry.t :=
  e <| raftpb.Entry.Term' := tm |>
    <| raftpb.Entry.Index' := word.add (word.add li (W64 1)) (W64 k) |>.

(** * The physical abstract state

    [nstate.t] is what [own_raft_phys r id s] ([inv_raft_phys.v]) is indexed
    by: the **most abstract description of the raft struct and the heap
    hanging off it that still lets every Go-level spec be stated on
    [own_raft_phys] alone**.  It is the first of three layers
    (notes/decisions.md, "Three layers"):

      Go code and heap  --own_raft_phys-->  [nstate.t]
      [nstate.t]        --nstate_rel----->  [pstate.t]  (election_protocol.v)
      [pstate.t]        --own_raft_ghost->  protocol properties

    **The rule.**  If a function cannot be specified with [own_raft_phys],
    refine [nstate.t] (and [own_raft_phys] with it) until it can.  Do *not*
    introduce a variant predicate -- a second ownership predicate for the
    struct, or one with an extra parameter -- for one caller's benefit.
    Until 2026-09-22 there were three ([own_raft_phys_at] with a free
    [r.step], [own_raft_bare] and [own_raft_notrk] with the tracker and/or the
    log cut out), and every spec stated on one of them was a spec its callers
    had to convert into and out of.  The three fields below that are not
    protocol state replace them:

    - [stepfn] is [r.step].  [becomeFollower] writes it *before* calling
      [reset], and [newRaft] calls [becomeFollower] while it is still nil,
      so it cannot be a function of [role].
    - [progress] is the progress map, id to [*Progress].  Nothing on the
      election path inserts into or deletes from it, so it is stable across
      every call, and a proof that borrows one peer's [Progress] can hand it
      back before a call and borrow it again after, at the same key.
    - [prvals] is each peer's [Progress] *value*, with its [Inflights]
      value: what [*pr] and [*pr.Inflights] hold for the [pr] that
      [progress] maps the peer to.  [own_tracker] is indexed by it
      ([inv_tracker.v]), so a spec says how it changes the [Progress]es,
      or quantifies the new values.  [maybeSendAppend] needs it: it reads
      [pr] before [r.send] and calls [pr.SentEntries] after, which panics
      in [StateSnapshot] and, through [Inflights.Add], on a full window --
      so it must know, after a call made with the struct sealed, that [pr]
      still holds what it read.  (Until 2026-09-29 that was done by a field
      [lent : option ProgressTracker.t]: the tracker's heap was *lent* out
      of [own_raft_phys] to the caller, and every function that touched the
      tracker took [lent = None]; before 2026-09-21, the variant predicate
      [own_raft_bare].  A proposed replacement, a "pin" recording one
      [Progress] value, was rejected: [nstate.t] holds only physical
      state.)
    - [log] is [r.raftLog], the log's location (it never changes).
    - [logst] is the log's state ([logstate.t]).

    The first six fields are exactly [pstate.t]'s, with the same names, so
    that a spec's [s.(nstate.term)] reads the same as it always did. *)
Module nstate.
Section defn.
Context {ext : ffi_syntax}.
Record t :=
  mk {
      term : w64;
      vote : w64;
      lead : w64;
      role : role.t;
      votes : gmap w64 bool;
      outbox : list msg.t;
      stepfn : func.t;                (** [r.step] *)
      progress : gmap w64 loc;        (** [r.trk.Progress], as a map *)
      log : loc;                      (** [r.raftLog] *)
      logst : logstate.t;             (** the log's abstract state *)
      prvals : gmap w64 (tracker.Progress.t * tracker.Inflights.t);
                                      (** [*pr], [*pr.Inflights], per peer *)
    }.
End defn.
#[global] Instance settable {ext : ffi_syntax} : Settable (@t ext) :=
  settable! (@mk ext) <term; vote; lead; role; votes; outbox; stepfn; progress; log; logst; prvals>.
End nstate.

Section phys_state.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type s : nstate.t.

(** Which of the three [stepX] functions [r.step] holds in each role.  The
    [becomeX] functions assign these, and [Step] dispatches a message it does
    not handle inline through [r.step(m)]. *)
Definition step_func_of (ro : role.t) : func.t :=
  match ro with
  | role.Follower => functions raft.stepFollower []
  | role.Candidate => functions raft.stepCandidate []
  | role.Leader => functions raft.stepLeader []
  end.

(** ** Transitions of the physical state

    Each mirrors a Go function exactly, [r.step] included, and leaves the
    fields the function does not write alone. *)

Definition send_msgs s (ms : list msg.t) : nstate.t :=
  s <| nstate.outbox := s.(nstate.outbox) ++ ms |>.

(** [reset(term)]: clears [Vote] only when the term actually changes, always
    clears [lead] and the tally. *)
Definition reset_to s (term : w64) : nstate.t :=
  s <| nstate.term := term |>
    <| nstate.vote := if decide (term = s.(nstate.term))
                      then s.(nstate.vote) else W64 0 |>
    <| nstate.lead := W64 0 |>
    <| nstate.votes := ∅ |>.

Definition become_follower s (term lead : w64) : nstate.t :=
  reset_to s term
    <| nstate.lead := lead |>
    <| nstate.role := role.Follower |>
    <| nstate.stepfn := step_func_of role.Follower |>.

Definition become_candidate (id : w64) s : nstate.t :=
  reset_to s (word.add s.(nstate.term) (W64 1))
    <| nstate.vote := id |>
    <| nstate.role := role.Candidate |>
    <| nstate.stepfn := step_func_of role.Candidate |>.

(** [becomeLeader] up to its [appendEntry]: what [reset], the [lead] and
    [state] writes and [r.step] leave. *)
Definition become_leader_pre (id : w64) s : nstate.t :=
  reset_to s s.(nstate.term)
    <| nstate.lead := id |>
    <| nstate.role := role.Leader |>
    <| nstate.stepfn := step_func_of role.Leader |>.

(** The empty entry a new leader appends ([pb.Entry{Data: nil}], the zero
    [Entry]), stamped at the leader's term and the log's next index. *)
Definition leader_entry s : raftpb.Entry.t :=
  stamp s.(nstate.term) (log_last s.(nstate.logst)) 0 (zero_val raftpb.Entry.t).

(** [becomeLeader]: [become_leader_pre], then the empty entry appended. *)
Definition become_leader (id : w64) s : nstate.t :=
  become_leader_pre id s
    <| nstate.logst := log_append s.(nstate.logst) [leader_entry s] |>.

(** ** The connection to the protocol state *)

Definition to_pstate s : pstate.t :=
  pstate.mk s.(nstate.term) s.(nstate.vote) s.(nstate.lead) s.(nstate.role)
            s.(nstate.votes) s.(nstate.outbox).

(** A physical state that can take a protocol step: [r.step] agrees with
    the role.  Every [becomeX] establishes it.  (Until 2026-09-29 it also
    said nothing was on loan, [nstate_idle s]: the tracker could be lent
    out of [own_raft_phys] ([nstate.lent]), and until earlier the same day
    a slice of the log ([logstate.page]).  Nothing is ever lent now.) *)
Definition nstate_wf s : Prop :=
  s.(nstate.stepfn) = step_func_of s.(nstate.role).

(** [s] refines the protocol state [ps]. *)
Definition nstate_rel s (ps : pstate.t) : Prop :=
  to_pstate s = ps ∧ nstate_wf s.

(** Each physical transition is its protocol counterpart on [to_pstate].
    All by computation; stated so that proofs rewrite rather than unfold. *)
Lemma to_pstate_send_msgs s ms :
  to_pstate (send_msgs s ms) = psend_msgs (to_pstate s) ms.
Proof. done. Qed.

Lemma to_pstate_become_follower s term lead :
  to_pstate (become_follower s term lead)
  = pbecome_follower (to_pstate s) term lead.
Proof. done. Qed.

(** [reset]'s conditional clear of the vote is overwritten by [vote := id]. *)
Lemma to_pstate_become_candidate id s :
  to_pstate (become_candidate id s) = pbecome_candidate id (to_pstate s).
Proof. done. Qed.

Lemma to_pstate_become_leader id s :
  to_pstate (become_leader id s) = pbecome_leader id (to_pstate s).
Proof. rewrite /become_leader /become_leader_pre /reset_to /to_pstate /= decide_True //. Qed.

Lemma to_pstate_votes s v :
  to_pstate (s <| nstate.votes := v |>) = to_pstate s <| pstate.votes := v |>.
Proof. done. Qed.

Lemma to_pstate_vote s v :
  to_pstate (s <| nstate.vote := v |>) = to_pstate s <| pstate.vote := v |>.
Proof. done. Qed.

Lemma nstate_wf_become_follower s term lead :
  nstate_wf (become_follower s term lead).
Proof. done. Qed.

Lemma nstate_wf_become_candidate id s :
  nstate_wf (become_candidate id s).
Proof. done. Qed.

Lemma nstate_wf_become_leader id s :
  nstate_wf (become_leader id s).
Proof. done. Qed.

(** A state with new [Progress] values is as well-formed as before: [r.step]
    and the role are untouched. *)
Lemma nstate_wf_prvals s pvs : nstate_wf s → nstate_wf (s <| nstate.prvals := pvs |>).
Proof. done. Qed.

Lemma to_pstate_prvals s pvs : to_pstate (s <| nstate.prvals := pvs |>) = to_pstate s.
Proof. done. Qed.

Lemma nstate_wf_send_msgs s ms : nstate_wf s → nstate_wf (send_msgs s ms).
Proof. done. Qed.

End phys_state.
