Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [appendEntry] stamps the current term and the next indices into the
    caller's batch, charges it against the uncommitted-entry budget, appends
    it to the log and then queues a self-addressed [MsgAppResp] at the new
    last index ([raft__appendEntryⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3446:
    [r.send(pb.Message{To: r.id, Type: pb.MsgAppResp, Index: li})], [li]
    what [raftLog.append] returned).  Since 2026-10-01 [MsgAppResp] has an
    abstraction, so the outbox grows by that message, [self_ack] ([defs.v]):
    the leader acknowledging its own append, which the model's [step_win]
    and [step_propose] send.  (Until then [mtype_of MsgAppResp = None] and
    the abstract outbox was unchanged.)

    Three pieces of history, because this claim has been wrong before.  Its
    form before 2026-09-15 owned only [own_raftLog] while the code it
    describes writes [r.msgsAfterAppend], which made it **false**; it could
    not be stated honestly before the outbox was abstracted, because the old
    [is_phys_msg] clause was unprovable for a [MsgAppResp].  Until
    2026-09-18 it was called [wp_raft__appendEmptyEntry], after a Go method
    that **does not exist** -- the method is [appendEntry].  Both are in
    notes/false-statements.md.  And until 2026-09-20 the triple was an
    [Axiom]: it is now proved.

    Two more things the first form of this triple got wrong, both found by
    review on 2026-09-18 and both the same old mistake -- a claim about the
    code that nobody had read the body for.

    **It took no ownership of [es].** The method writes [Term] and [Index]
    into *every element* of the slice ([raft__appendEntryⁱᵐᵖˡ]'s
    [slice.for_range], v3.v:3453-3461), so a triple that does not own [es]
    asserts the safety of a write to memory it has no claim on -- the
    [wp_ProgressTracker__Visit] mistake again, one level out: not "own the
    receiver's fields" but "own what you write".  [es ↦* ents] is now a
    precondition.  It comes back: [raftLog.append] copies the entry
    *values* into [unstable.entries], so the caller's slice is not consumed
    -- and since 2026-09-25 it comes back *named*, as the stamped batch
    ([stamp], protocol.v): [Term := r.Term] and [Index := lastIndex()+1+k]
    in element [k].  (Until the log's state was in [nstate.t] the witness
    was existential, because naming it would have pinned the log's length.)

    **It claimed [RET #true] unconditionally**, and [appendEntry] does have a
    [return: #false] -- the path where [increaseUncommittedSize] rejects the
    batch (v3.v:3469).  The fix is *not* to make the result existential.
    [becomeLeader], the only caller in scope, does

        if !r.appendEntry(pb.Entry{Data: nil}) { r.logger.Panic(…) }

    and [wp_Logger__logf] deliberately excludes [Panic], so a bare
    existential result makes [becomeLeader] unprovable rather than merely
    weaker.  What is true is that the reject path is unreachable *for an
    empty payload*: [increaseUncommittedSize] returns [false] only when

        uncommittedSize > 0 ∧ payloadsSize(ents) > 0 ∧ … > maxUncommittedSize

    ([raft__increaseUncommittedSizeⁱᵐᵖˡ], v3.v:5401), and
    [payloadsSize] sums [len(e.Data)] (v3.v:7515,7524).

    From 2026-09-18 to 2026-10-01 that was a *premise* ([Hempty]) and the
    result was [RET #true].  Since 2026-10-01 the triple takes an arbitrary
    [EntryNormal] batch -- what [stepLeader]'s [MsgProp] arm passes, and
    what the model's [step_propose] describes -- so the result is a bool
    [accepted], and the fact above is a *conjunct* of the postcondition:
    [Forall (Data empty) ents → accepted = true].  That is as far as
    acceptance can be pinned: the exact condition reads [r.uncommittedSize]
    and [r.maxUncommittedSize], which [nstate.t] does not hold.
    [becomeLeader] destructs [accepted] and kills the [false] branch with
    the implication, so its [Panic] is still demonstrably dead code.

    *** The two paths (read against the body, 2026-10-01)

    The stamping loop (v3.v:3456) runs *before* [increaseUncommittedSize]
    (v3.v:3463), so the caller's slice is stamped on both paths and
    [es ↦* imap (stamp …) ents] is outside the [if].  The reject path
    (v3.v:3466-3469) reads [r.id] and [r.logger], calls [Warningf], and
    returns [false]: nothing in the struct is written, so it comes back at
    [s].  The accept path writes [r.uncommittedSize] (which [own_raft_phys]
    does not pin), appends, and sends the self-ack.  (The named result
    [accepted], v3.v:3448, is allocated and never read: both exits are
    [return: #b].)

    *** The premises

    Both are what the *log* needs:

    - [Hnorm]: no entry in the batch is a configuration change.
      [own_raftLog]'s [HnoConfChange] is about the whole log, so appending
      an [EntryConfChange] would break it.  [becomeLeader] passes
      [pb.Entry{Data: nil}], whose [Type] is the zero value [EntryNormal].
      (Note the method does *not* set [Type] -- only [Term] and [Index] --
      so the caller's value is what lands in the log.)
    - [Hsmall]: the batch has fewer than [2^61] entries, so that
      [lastIndex()+1+k] does not wrap while the loop stamps it in.

    *** The no-wrap gap, and how it is closed

    Handing [own_raft_phys] back after [raftLog.append] also asserts
    [own_raftLog]'s [Hnowrap] -- that
    [prev.index + |sents| + |uents| + 1 < 2^64] still holds for the *longer*
    log.  The pre-state gives that bound at the old length, so until
    2026-09-20 this triple was an axiom with a documented over-claim, and the
    plan recorded here was to make it a premise and thread it through
    [becomeLeader] to [Step].

    **That plan does not work, and the reason is worth writing down.**  A
    premise of [becomeLeader] (or of [Step]) may mention only [cfg], [r],
    [id] and [s]; the log's length is existentially quantified *inside*
    [own_raft_phys], so no premise at those specs can say anything about it.
    Threading would therefore have meant exposing the log's last index in
    every spec from here up to [Step] -- or indexing [own_raft_phys] by it,
    which is 95 call sites.  Nor can the bound be an invariant of the log:
    any property preserved by [append] is closed under [+1] at the last
    index and so bounds nothing (this is why the "fixed slack" idea fails --
    a slack constant shrinks by one on every append).

    What is true is that the log's last index splits into a part [append]
    moves and a part it does not.  [|uents|] is the length of the Go slice
    [unstable.entries], and Perennial's [own_slice_len] bounds *any* slice's
    length by [2^63] -- re-derived from the new slice after the [append],
    so it is inductive for free.  [prev.index + |sents|] is the compaction
    boundary plus the stable prefix, which lives behind the client-supplied
    [Storage] and which nothing on this path changes.  So the assumption was
    put where it belongs: [is_Storage]'s [Hbounded] clause
    ([inv_storage.v]) says the stable log's last index is below [2^61].
    With it, and with [Hsmall], the log's last index stays below
    [2^61 + 2^63] and the append cannot wrap -- no caller obligation, and
    [becomeLeader]'s spec is unchanged.

    *** The rest of the body

    [increaseUncommittedSize] writes [r.uncommittedSize], a field
    [own_raft_phys] does not mention; [traceReplicate] is a literal no-op
    (v3.v:6364); and the [MsgAppResp] is [send_ok]'s [MsgAppResp] clause,
    which allows it to be self-addressed.

    *** The log in the postcondition

    Since 2026-09-25 the log's state is in [nstate.t], so the
    postcondition says exactly what was appended: the batch, stamped with
    the current term and consecutive indices after [lastIndex()]
    ([stamp], [log_last], [log_append], [defs.v]).  Until then it returned
    the struct at the *same* state, which was only true because
    [own_raft_phys] quantified the log away. *)
Definition wp_raft__appendEntry_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64),
  ∀ (r : loc) id s (es : slice.t) (ents : list raftpb.Entry.t),
  (* no configuration change, so the log's [HnoConfChange] survives *)
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (* a batch small enough that [lastIndex()+1+k] does not wrap *)
  (Z.of_nat (length ents) < 2^61)%Z →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s ∗ es ↦* ents }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ (accepted : bool), RET #accepted;
      (* an all-empty batch is never dropped -- see above *)
      ⌜ Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) ents →
        accepted = true ⌝ ∗
      (* stamped on both paths: the loop runs before the budget check *)
      es ↦* imap (stamp s.(nstate.term) (log_last s.(nstate.logst))) ents ∗
      if accepted then
        own_raft_phys cfg r id
          (send_msgs
             (s <| nstate.logst := log_append s.(nstate.logst)
                    (imap (stamp s.(nstate.term) (log_last s.(nstate.logst))) ents) |>)
             [self_ack id
                (s <| nstate.logst := log_append s.(nstate.logst)
                       (imap (stamp s.(nstate.term) (log_last s.(nstate.logst))) ents) |>)])
      else
        (* dropped: [Warningf] and [return false], nothing written *)
        own_raft_phys cfg r id s }}}.

Module Type RAFT__APPENDENTRY.
  Parameter wp_raft__appendEntry : wp_raft__appendEntry_body.
  Arguments wp_raft__appendEntry {_ _ _ _ _ _ _ _}.
End RAFT__APPENDENTRY.
