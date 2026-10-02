Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** * [raft.handleAppendEntries]

    The follower's handling of a [MsgApp] ([raft__handleAppendEntriesⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:4877; raft.go:1778).  Three exits, in
    the order the body takes them:

    1. [a.prev.index < r.raftLog.committed] (stale): send
       [MsgAppResp{To: m.From, Index: committed}] and return;
    2. [r.raftLog.maybeAppend(a, m.Commit)] answers [ok]: send
       [MsgAppResp{To: m.From, Index: mlastIndex}] and return;
    3. otherwise (reject): a [Debugf] whose arguments call
       [zeroTermOnOutOfBounds(term(m.Index))] -- with [m.Index] possibly
       past the last index, so [term] may return [ErrUnavailable]; see
       [spec_raftLog__zeroTermOnOutOfBounds.v] -- then
       [hintIndex, hintTerm := findConflictByTerm(min(m.Index, lastIndex()), m.LogTerm)]
       and [MsgAppResp{To: m.From, Index: m.Index, Reject: true,
       RejectHint: hintIndex, LogTerm: hintTerm}].

    No exit writes a raft field: the struct changes only through the log
    ([maybeAppend]) and the outbox ([send]).

    **The messages, as [send] queues them** ([send_ok]'s [MsgAppResp]
    clause (d), [spec_raft__send.v]): [From] stamped [id], [Term] stamped
    [s.term], [Entries] nil (so [ents = []]), every field the literal does
    not name zero.  So the abstraction of the literal [m'] is
    [abs_msg_from mtype.AppResp m' id s.term []], i.e. [app_resp] below --
    exactly the messages [protocol.v]'s [step_app_stale] /
    [step_app_accept] / [step_app_reject] send ([msg.mk mtype.AppResp id
    m.from term reject index logterm (W64 0) rejecthint []]), with
    [logterm := hintTerm] and [rejecthint := hintIndex] on a rejection and
    [0] for both otherwise. *)

(** The [MsgAppResp] [handleAppendEntries] queues, as the model sees it:
    [msg.mk ty from to term reject index logterm commit rejecthint entries]. *)
Definition app_resp {ext : ffi_syntax} (id : w64) (s : nstate.t) (to : w64) (reject : bool)
    (index hintterm hint : w64) : msg.t :=
  msg.mk mtype.AppResp id to s.(nstate.term) reject index hintterm (W64 0) hint [].

(** The three exits, as a relation between the state [s] the call starts
    in and the state [s'] it ends in.  The disjuncts are exclusive: the
    first on [m.Index < committed], the second and third on whether
    [(m.LogTerm, m.Index)] matches the log ([plog_maybe_append] is [None]
    exactly when it does not).

    - stale: the reply carries [committed];
    - accept: the log is [maybeAppend]'s new log -- [prev] and [applied]
      unchanged, the entries [plog_maybe_append]'s, [committed] raised to
      [min(m.Commit, lastnewi)] ([plog_commit_to]) -- and the reply
      carries [lastnewi].  [ls'] is existential because [maybeAppend]'s
      spec says no more about the [sents]/[uents] split;
    - reject: state unchanged but for the reply; the hint is *some*
      [(hint, hintterm)] ([findConflictByTerm]'s spec pins only
      [hint ≤ min(m.Index, lastIndex())], and the model allows any). *)
Definition handle_app_result {ext : ffi_syntax} (id : w64) (s : nstate.t)
    (m : raftpb.Message.t) (ents : list raftpb.Entry.t) (s' : nstate.t) : Prop :=
  let ls := s.(nstate.logst) in
  let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
  let prev := raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index') in
  let to := m.(raftpb.Message.From') in
  (uint.Z m.(raftpb.Message.Index') < uint.Z ls.(logstate.committed) ∧
   s' = send_msgs s [app_resp id s to false ls.(logstate.committed) (W64 0) (W64 0)])
  ∨
  (uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') ∧
   ∃ (lastnewi : w64) (es' : list raftpb.Entry.t) (ls' : logstate.t),
     plog_maybe_append ls.(logstate.prev) es prev ents = Some (lastnewi, es') ∧
     ls'.(logstate.prev) = ls.(logstate.prev) ∧
     ls'.(logstate.sents) ++ ls'.(logstate.uents) = es' ∧
     ls'.(logstate.applied) = ls.(logstate.applied) ∧
     ls'.(logstate.committed) =
       plog_commit_to ls.(logstate.committed)
         (if decide (uint.Z m.(raftpb.Message.Commit') < uint.Z lastnewi)%Z
          then m.(raftpb.Message.Commit') else lastnewi) ∧
     s' = send_msgs (s <| nstate.logst := ls' |>)
            [app_resp id s to false lastnewi (W64 0) (W64 0)])
  ∨
  (uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') ∧
   ¬ plog_matches ls.(logstate.prev) es prev ∧
   ∃ (hint hintterm : w64),
     s' = send_msgs s [app_resp id s to true m.(raftpb.Message.Index') hintterm hint]).

(** Premises -- [maybeAppend]'s ([spec_raftLog__maybeAppend.v]), restated
    at the message, since [a = logSliceFromMsgApp(&m)] is
    [{term: m.Term, prev: (m.LogTerm, m.Index), entries: m.Entries}]:

    - the batch is a well-formed log slice after [(m.LogTerm, m.Index)],
      does not wrap, and holds no configuration change;
    - **the conflict fact**, as hypothetical as the code allows: only when
      the stale test has failed ([committed ≤ m.Index]) and the prefix
      matches is [maybeAppend]'s [Panicf] reachable, and there the
      conflict index must be [0] or above [committed]
      ([app_no_conflict_below_commit], [protocol.v]);
    - the [Entries] slice read-only with its capacity owned, because
      [maybeAppend] may adopt it as the unstable suffix.  On the other
      two exits the capacity is simply dropped.

    Not needed, and so not premises: [m.Type = MsgApp] (the body never
    reads it), [m.From ≠ 0] and [m.To = id] (no panic depends on them;
    [send]'s [MsgAppResp] clause allows any [To], the node itself
    included), [m.Term] (only [a.term], which nothing reads). *)
Definition wp_raft__handleAppendEntries_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (m : raftpb.Message.t) (ents : list raftpb.Entry.t),
  plog_wf (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) ents →
  (uint.Z m.(raftpb.Message.Index') + Z.of_nat (length ents) + 1 < 2^64)%Z →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (let ls := s.(nstate.logst) in
   let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
   uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') →
   plog_matches ls.(logstate.prev) es
     (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
   plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
   uint.Z ls.(logstate.committed) < uint.Z (plog_find_conflict ls.(logstate.prev) es ents))%Z →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
      "Hcap" ∷ own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) }}}
    r @! (go.PointerType raft.raft) @! "handleAppendEntries" #m
  {{{ (s' : nstate.t), RET #();
      own_raft_phys cfg r id s' ∗ ⌜ handle_app_result id s m ents s' ⌝ }}}.

Module Type RAFT__HANDLEAPPENDENTRIES.
  Parameter wp_raft__handleAppendEntries : wp_raft__handleAppendEntries_body.
  Arguments wp_raft__handleAppendEntries {_ _ _ _ _ _ _ _}.
End RAFT__HANDLEAPPENDENTRIES.
