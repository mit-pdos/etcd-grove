Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.maybeSendAppend(to, sendIfEmpty)] -- at most one [MsgApp] to one peer
    ([raft__maybeSendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3096).

    It can do four different things, and the postcondition is deliberately
    the weakest statement true of all four:

      - [pr.IsPaused()] -> nothing sent, [false];
      - [r.raftLog.term(pr.Next-1)] errors -> [maybeSendSnapshot], which
        sends a [MsgSnap] (model-invisible) or nothing;
      - no entries and [!sendIfEmpty] -> nothing sent, [false];
      - otherwise one [MsgApp] to [to] at [r.Term].

    So: the outbox grows by *some* list of messages [repl_ok] allows
    ([protocol.v]: an [App] from [id] to [to] at the current term, carrying
    entries of the log and a commit index no larger than the log's, or a
    [Snap]) -- in fact zero or one, but nothing above needs that, and
    saying "one" would be false.  This is the same weakening as
    [wp_raft__bcastAppend]'s.  (Until 2026-10-01: [app_sends], [App]s
    with only the sender and term pinned.)

    The premises.  [to ≠ id] is what [send_ok]'s [MsgApp] clause needs
    ([send] panics on a self-addressed [MsgApp]); [bcastAppend]'s closure
    tests [id == r.id] and returns first.  [to ∈ cfg] is what makes
    [r.trk.Progress[to]] hit: a miss returns the zero [*Progress], i.e.
    [null], and the [pr.IsPaused()] that follows would dereference it.
    [Visit] only enumerates voters, so [bcastAppend] has it. *)
Definition wp_raft__maybeSendAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (to : w64)
    (sendIfEmpty : bool),
  to ≠ id →
  to ∈ cfg →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "maybeSendAppend" #to #sendIfEmpty
  {{{ (b : bool) (ms : list msg.t) pvs, RET #b;
      own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
      ⌜ repl_sends id s ms ⌝ ∗
      (* [SentEntries], [SentCommit], [BecomeSnapshot] leave [Match] alone *)
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.

Module Type RAFT__MAYBESENDAPPEND.
  Parameter wp_raft__maybeSendAppend : wp_raft__maybeSendAppend_body.
  Arguments wp_raft__maybeSendAppend {_ _ _ _ _ _ _ _}.
End RAFT__MAYBESENDAPPEND.
