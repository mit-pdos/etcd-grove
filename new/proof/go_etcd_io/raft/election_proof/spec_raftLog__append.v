Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.append(ents)]: splice a batch into the log, truncating whatever it
    overwrites, and return the new last index
    ([raftLog__appendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:599).

        if len(ents) == 0 { return l.lastIndex() }
        if after := ents[0].Index - 1; after < l.committed {
            l.logger.Panicf("after(%d) is out of range [committed(%d)]", …)
        }
        l.unstable.truncateAndAppend(ents)
        return l.lastIndex()

    **Widened 2026-10-01** from "the batch continues the log" to any batch
    starting inside or right after it, which is what [maybeAppend] needs
    (it appends the suffix of a [MsgApp] from the first conflict on).  The
    new state is [log_truncate_append ls ents] ([inv_raftlog.v]); its
    entries are [plog_truncate_append prev (sents ++ uents) ents]
    ([plog.v]), which the postcondition states.  A batch starting in the
    stable part shrinks the visible stable part [sents] and becomes the
    whole unstable suffix (the shadowed storage tail stays in [Storage]).

    Premises (for a non-empty batch, [e0 = ents[0]]):

    - [committed < e0.Index <= lastIndex() + 1]: the upper bound is
      [truncateAndAppend]'s (a gap would be a [Panicf] in [u.slice]); the
      lower bound makes the [Panicf] above dead ([after = e0.Index - 1 >=
      committed]) -- the protocol fact "an accepted [MsgApp] never
      rewrites a committed entry" ([raft-replication-model.md],
      "Protocol facts the code needs") -- and keeps [committed] inside the
      new log;
    - contiguous indices from [e0.Index] and [e0.Index + |ents| < 2^64]:
      the new log is [log_indices_ok] and does not wrap.  [own_raftLog]
      cannot carry a bound that survives a longer log (inv_raftlog.v), so
      the caller supplies it;
    - no configuration change in the batch ([HnoConfChange]'s scope).

    **The batch**: lent and returned unless [log_adopts ls ents] -- the
    batch starts at or below the unstable offset without continuing the
    suffix -- in which case [truncateAndAppend] adopts the slice itself as
    [u.entries], and the caller hands it over read-only with its capacity
    ([spec_unstable__truncateAndAppend.v]).  [appendEntry]'s batch
    continues the log, so for it [log_adopts] is [false]
    ([log_truncate_append_cont]). *)
Definition wp_raftLog__append_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (ents : list raftpb.Entry.t)
    (es : slice.t) (dq : dfrac),
  (∀ e0, ents !! 0%nat = Some e0 →
     (uint.Z ls.(logstate.committed) < uint.Z e0.(raftpb.Entry.Index')
      ≤ uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
        + Z.of_nat (length ls.(logstate.uents)) + 1)%Z ∧
     (∀ (k : nat) e, ents !! k = Some e →
        uint.Z e.(raftpb.Entry.Index') = uint.Z e0.(raftpb.Entry.Index') + k)%Z ∧
     (uint.Z e0.(raftpb.Entry.Index') + Z.of_nat (length ents) < 2^64)%Z) →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗
      "Hes" ∷ es ↦*{dq} ents ∗
      "Hadopt" ∷ (if log_adopts ls ents
                  then ⌜ dq = DfracDiscarded ⌝ ∗ own_slice_cap raftpb.Entry.t es (DfracOwn 1)
                  else True) }}}
    l @! (go.PointerType raft.raftLog) @! "append" #es
  {{{ (li : w64), RET #li;
      own_raftLog l (log_truncate_append ls ents) ∗
      (if log_adopts ls ents then True else es ↦*{dq} ents) ∗
      ⌜ (log_truncate_append ls ents).(logstate.sents)
          ++ (log_truncate_append ls ents).(logstate.uents)
        = plog_truncate_append ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents)) ents ∧
        (uint.Z li = uint.Z ls.(logstate.prev).(raft.entryID.index')
                     + Z.of_nat (length (log_truncate_append ls ents).(logstate.sents))
                     + Z.of_nat (length (log_truncate_append ls ents).(logstate.uents)))%Z ⌝ }}}.

Module Type RAFTLOG__APPEND.
  Parameter wp_raftLog__append : wp_raftLog__append_body.
  Arguments wp_raftLog__append {_ _ _ _ _ _ _ _}.
End RAFTLOG__APPEND.
