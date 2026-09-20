Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [l.append(ents)]: add a batch to the end of the log, returning the new
    last index ([raftLog__appendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:599).

    The body is short and has one panic:

        if len(ents) == 0 { return l.lastIndex() }
        if after := ents[0].Index - 1; after < l.committed {
            l.logger.Panicf("after(%d) is out of range [committed(%d)]", …)
        }
        l.unstable.truncateAndAppend(ents)
        return l.lastIndex()

    Stated at a fixed split ([_at]), like every other [raftLog] spec, because
    the postcondition has to *name* the new split -- [uents ++ ents].

    The premises are what makes the batch a legal continuation of the log,
    and they are exactly what discharges the [Panicf]:

    - [Hidx]: the whole log, batch included, still has contiguous indices
      from [prev.index+1].  In particular [ents[0].Index] is
      [prev.index+|sents|+|uents|+1], so [after] is the current last index,
      which is [≥ l.committed] by [own_raftLog_at]'s [Hcommitted] -- the
      panic is dead code, not assumed away.  It also fixes the [after]
      subtraction: [ents[0].Index ≥ 1], so it does not wrap.
    - [Hnorm]: the batch holds no configuration change, which is what keeps
      [own_raftLog_at]'s [HnoConfChange] true of the longer log.  Under this
      development's scope no configuration change is ever proposed
      ([inv_raftlog.v]), so a caller supplies it from the entry it built.
    - [Hnowrap]: the *new* last index still leaves room, i.e.
      [prev.index + |sents| + |uents| + |ents| + 1 < 2^64].  [own_raftLog_at]
      asserts this bound at the old length and a longer log needs it at the
      new one, so it cannot be derived and has to be asked for.  See
      [spec_raft__appendEntry.v] for where the caller gets it.

    The batch is *lent*: [truncateAndAppend] copies the entry values into
    [unstable.entries], so [es] comes back at the caller's fraction. *)
Definition wp_raftLog__append_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (prev : raft.entryID.t) (sents uents ents : list raftpb.Entry.t)
    (es : slice.t) (dq : dfrac),
  log_indices_ok prev (sents ++ uents ++ ents) →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents) + Z.of_nat (length ents) + 1 < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents ∗
      "Hes" ∷ es ↦*{dq} ents }}}
    l @! (go.PointerType raft.raftLog) @! "append" #es
  {{{ (li : w64), RET #li;
      own_raftLog_at l prev sents (uents ++ ents) ∗ es ↦*{dq} ents ∗
      ⌜ (uint.Z li = uint.Z prev.(raft.entryID.index')
                     + Z.of_nat (length sents) + Z.of_nat (length uents)
                     + Z.of_nat (length ents))%Z ⌝ }}}.

Module Type RAFTLOG__APPEND.
  Parameter wp_raftLog__append_at : wp_raftLog__append_at_body.
  Arguments wp_raftLog__append_at {_ _ _ _ _ _ _ _}.
End RAFTLOG__APPEND.
