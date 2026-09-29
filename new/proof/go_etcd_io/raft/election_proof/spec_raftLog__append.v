Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.append(ents)]: add a batch to the end of the log, returning the new
    last index ([raftLog__appendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:599).

    The body is short and has one panic:

        if len(ents) == 0 { return l.lastIndex() }
        if after := ents[0].Index - 1; after < l.committed {
            l.logger.Panicf("after(%d) is out of range [committed(%d)]", …)
        }
        l.unstable.truncateAndAppend(ents)
        return l.lastIndex()

    The postcondition *names* the new state: [ls] with [uents ++ ents] as
    the unstable suffix.

    The premises are what makes the batch a legal continuation of the log,
    and they are exactly what discharges the [Panicf]:

    - [Hidx]: the whole log, batch included, still has contiguous indices
      from [prev.index+1].  In particular [ents[0].Index] is
      [prev.index+|sents|+|uents|+1], so [after] is the current last index,
      which is [≥ l.committed] by [own_raftLog]'s [Hcommitted] -- the
      panic is dead code, not assumed away.  It also fixes the [after]
      subtraction: [ents[0].Index ≥ 1], so it does not wrap.
    - [Hnorm]: the batch holds no configuration change, which is what keeps
      [own_raftLog]'s [HnoConfChange] true of the longer log.  Under this
      development's scope no configuration change is ever proposed
      ([inv_raftlog.v]), so a caller supplies it from the entry it built.
    - [Hnowrap]: the *new* last index still leaves room, i.e.
      [prev.index + |sents| + |uents| + |ents| + 1 < 2^64].  [own_raftLog]
      asserts this bound at the old length and a longer log needs it at the
      new one, so it cannot be derived and has to be asked for.  See
      [spec_raft__appendEntry.v] for where the caller gets it.

    The batch is *lent*: [truncateAndAppend] copies the entry values into
    [unstable.entries], so [es] comes back at the caller's fraction. *)
Definition wp_raftLog__append_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (ents : list raftpb.Entry.t)
    (es : slice.t) (dq : dfrac),
  log_indices_ok ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents) ++ ents) →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
   + Z.of_nat (length ls.(logstate.uents)) + Z.of_nat (length ents) + 1 < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗
      "Hes" ∷ es ↦*{dq} ents }}}
    l @! (go.PointerType raft.raftLog) @! "append" #es
  {{{ (li : w64), RET #li;
      own_raftLog l (ls <| logstate.uents := ls.(logstate.uents) ++ ents |>) ∗ es ↦*{dq} ents ∗
      ⌜ (uint.Z li = uint.Z ls.(logstate.prev).(raft.entryID.index')
                     + Z.of_nat (length ls.(logstate.sents)) + Z.of_nat (length ls.(logstate.uents))
                     + Z.of_nat (length ents))%Z ⌝ }}}.

Module Type RAFTLOG__APPEND.
  Parameter wp_raftLog__append : wp_raftLog__append_body.
  Arguments wp_raftLog__append {_ _ _ _ _ _ _ _}.
End RAFTLOG__APPEND.
