Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** Out of scope: the empty entry a new leader appends.  [appendEntry]
    updates the log and then queues a self-addressed [MsgAppResp]
    ([new/code/go_etcd_io/raft/v3.v], the [send] at the end of
    [raft__appendEntryⁱᵐᵖˡ]).  [mtype_of MsgAppResp = None], so [abs_msg_opt]
    drops it and the abstract state — outbox included — is unchanged.

    It is discharged by an [Axiom] inside [proof_raft__appendEntry.v]'s
    functor, which is how a trust-boundary triple is carried here — the
    keyword still makes it an assumption under [Print Assumptions].

    Two pieces of history, because this claim has been wrong before.  Its
    form before 2026-09-15 owned only [own_raftLog] while the code it
    describes writes [r.msgsAfterAppend], which made it **false**; it could
    not be stated honestly before the outbox was abstracted, because the old
    [is_phys_msg] clause was unprovable for a [MsgAppResp].  And until
    2026-09-18 it was called [wp_raft__appendEmptyEntry], after a Go method
    that **does not exist** — the method is [appendEntry].  Both are in
    notes/false-statements.md.

    Two more things the first form of this triple got wrong, both found by
    review on 2026-09-18 and both the same old mistake -- a claim about the
    code that nobody had read the body for.

    **It took no ownership of [es].** The method writes [Term] and [Index]
    into *every element* of the slice ([raft__appendEntryⁱᵐᵖˡ]'s
    [slice.for_range], v3.v:3453-3461), so a triple that does not own [es]
    asserts the safety of a write to memory it has no claim on -- the
    [wp_ProgressTracker__Visit] mistake again, one level out: not "own the
    receiver's fields" but "own what you write".  [es ↦* ents] is now a
    precondition and comes back existentially quantified, since the method
    has overwritten two fields of each entry.  It does come back:
    [raftLog.append] copies the entry *values* into [unstable.entries], so
    the caller's slice is not consumed.

    **It claimed [RET #true] unconditionally**, and [appendEntry] does have a
    [return: #false] -- the path where [increaseUncommittedSize] rejects the
    batch (v3.v:3463).  The fix is *not* to make the result existential.
    [becomeLeader], the only caller in scope, does

        if !r.appendEntry(pb.Entry{Data: nil}) { r.logger.Panic(…) }

    and [wp_Logger__logf] deliberately excludes [Panic], so an existential
    result makes [becomeLeader] unprovable rather than merely weaker.  What
    is actually true is that the reject path is unreachable *for an empty
    payload*: [increaseUncommittedSize] returns [false] only when

        uncommittedSize > 0 ∧ payloadsSize(ents) > 0 ∧ … > maxUncommittedSize

    ([raft__increaseUncommittedSizeⁱᵐᵖˡ], v3.v:5401), and
    [payloadsSize] sums [len(e.Data)] (v3.v:7515,7524).  So the premise below
    -- every entry's [Data] is empty, which is exactly what [becomeLeader]
    passes -- is what makes [RET #true] honest, and it is also what makes the
    [Panic] demonstrably dead code rather than assumed away.

    **One over-claim is left, deliberately, and whoever discharges this axiom
    inherits it.**  Handing [own_raft_phys] back after [raftLog.append] also
    asserts [own_raftLog_at]'s [Hnowrap]: that
    [prev.index + |sents| + |uents| + 1 < 2^64] still holds *after* one more
    entry, i.e. that the log index does not wrap.  The pre-state gives that
    bound at the old length, not the new one, so this does not follow -- it
    is the same shape as [campaign]'s term wrap (notes/STATUS.md, "Known
    broken"), which had to become a premise.  Repairing it means a no-wrap
    premise here and an obligation on [becomeLeader] to supply it; not done,
    because the fix has a caller obligation and this is the last core-raft
    axiom on the election path anyway.  The rest of the body is accounted
    for: [increaseUncommittedSize] adds a zero payload, so
    [r.uncommittedSize] is unchanged; [traceReplicate] is a literal no-op
    ([v3.v:6364]); the appended entry's [Type] is the zero value
    [EntryNormal], so [own_raftLog]'s [HnoConfChange] survives; and the
    [MsgAppResp] has no [mtype_of], so the abstract outbox is unchanged. *)
Definition wp_raft__appendEntry_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64),
  ∀ (r : loc) id s (es : slice.t) (ents : list raftpb.Entry.t),
  (* empty payloads, so [increaseUncommittedSize] cannot reject -- see above *)
  Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) ents →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s ∗ es ↦* ents }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ (ents' : list raftpb.Entry.t), RET #true;
      own_raft_phys cfg r id s ∗ es ↦* ents' }}}.

Module Type RAFT__APPENDENTRY.
  Parameter wp_raft__appendEntry : wp_raft__appendEntry_body.
  Arguments wp_raft__appendEntry {_ _ _ _ _ _ _ _}.
End RAFT__APPENDENTRY.
