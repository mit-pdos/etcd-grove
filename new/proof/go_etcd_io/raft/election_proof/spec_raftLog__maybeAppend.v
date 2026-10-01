Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.maybeAppend(a, committed)]: a follower's handling of a [MsgApp]'s
    entries -- [plog_maybe_append] ([plog.v]) plus the commit.

    The body ([raftLog__maybeAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:546):

        if !l.matchTerm(a.prev) { return 0, false }
        lastnewi = a.prev.index + uint64(len(a.entries))
        ci := l.findConflict(a.entries)
        switch {
        case ci == 0:
        case ci <= l.committed: l.logger.Panicf(...)
        default:
            offset := a.prev.index + 1
            if ci-offset > uint64(len(a.entries)) { l.logger.Panicf(...) }
            l.append(a.entries[ci-offset:]...)
        }
        l.commitTo(min(committed, lastnewi))
        return lastnewi, true

    Postcondition: when [a.prev] does not match, [(0, false)] and the log
    unchanged; otherwise [(lastnewi, true)], the entries are
    [plog_maybe_append]'s, and [committed] is raised to
    [min(committed, lastnewi)] ([plog_commit_to]).

    Premises, one per way the body could go wrong:
    - the batch is a well-formed log slice after [a.prev]
      ([plog_wf a.prev ents]) and [a.prev.index + |ents| + 1 < 2^64]: what
      [findConflict], [append] and the no-wrap of the new log need; it
      also makes the second [Panicf] ([ci - offset > len]) dead -- the
      design's "arithmetic" fact;
    - **the conflict fact** ([raft-replication-model.md], "Protocol facts
      the code needs", [app_no_conflict_below_commit]): if [a.prev]
      matches, the conflict index is [0] or above [committed].  It kills
      the first [Panicf] and is [append]'s [committed < ents[0].Index];
    - no configuration change in the batch ([append]'s scope premise).
    [commitTo]'s premise is *not* a premise here: after the append the
    log reaches [lastnewi], so [min(committed, lastnewi)] is inside it.

    **The batch's slice** is taken read-only with its capacity, and the
    capacity is not returned: [append] may adopt [a.entries[ci-offset:]]
    as [u.entries] ([spec_raftLog__append.v]), after which raft's own later
    [append]s write into its slack.  So the caller must own that slack
    (for a [MsgApp] handed to [Step], the message's [Entries] buffer). *)
Definition wp_raftLog__maybeAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (a : raft.logSlice.t) (ents : list raftpb.Entry.t)
    (committed : w64),
  plog_wf a.(raft.logSlice.prev') ents →
  (uint.Z a.(raft.logSlice.prev').(raft.entryID.index') + Z.of_nat (length ents) + 1 < 2^64)%Z →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (plog_matches ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents))
     a.(raft.logSlice.prev') →
   plog_find_conflict ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents)) ents
     = W64 0 ∨
   (uint.Z ls.(logstate.committed)
    < uint.Z (plog_find_conflict ls.(logstate.prev)
                (ls.(logstate.sents) ++ ls.(logstate.uents)) ents))%Z) →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗
      "#Hents" ∷ a.(raft.logSlice.entries') ↦*□ ents ∗
      "Hcap" ∷ own_slice_cap raftpb.Entry.t a.(raft.logSlice.entries') (DfracOwn 1) }}}
    l @! (go.PointerType raft.raftLog) @! "maybeAppend" #a #committed
  {{{ (lastnewi : w64) (ok : bool) (ls' : logstate.t), RET (#lastnewi, #ok);
      own_raftLog l ls' ∗
      ⌜ match plog_maybe_append ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents))
                a.(raft.logSlice.prev') ents with
        | None => ok = false ∧ lastnewi = W64 0 ∧ ls' = ls
        | Some (lni, es') =>
            ok = true ∧ lastnewi = lni ∧
            ls'.(logstate.prev) = ls.(logstate.prev) ∧
            ls'.(logstate.sents) ++ ls'.(logstate.uents) = es' ∧
            ls'.(logstate.applied) = ls.(logstate.applied) ∧
            ls'.(logstate.committed) =
              plog_commit_to ls.(logstate.committed)
                (if decide (uint.Z committed < uint.Z lni)%Z then committed else lni)
        end ⌝ }}}.

Module Type RAFTLOG__MAYBEAPPEND.
  Parameter wp_raftLog__maybeAppend : wp_raftLog__maybeAppend_body.
  Arguments wp_raftLog__maybeAppend {_ _ _ _ _ _ _ _}.
End RAFTLOG__MAYBEAPPEND.
