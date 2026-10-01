Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.increaseUncommittedSize(ents)]: charge a batch against the
    uncommitted-entries budget, and say whether it fits
    ([raft__increaseUncommittedSizeⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:5393).

    The body is

        s := payloadsSize(ents)
        if r.uncommittedSize > 0 && s > 0 && r.uncommittedSize+s > r.maxUncommittedSize {
            return false
        }
        r.uncommittedSize += s
        return true

    so with an all-empty batch ([payloadsSize] is then [0], see
    [spec_payloadsSize.v]) the *middle* conjunct is false whatever the
    budget holds and the reject path is **unreachable**.  That is the fact
    [appendEntry] needs to show its own [return false] -- and hence
    [becomeLeader]'s [logger.Panic] -- is dead code, and it is what the
    postcondition's implication says.

    Since 2026-10-01 the triple takes an *arbitrary* batch (until then it
    required the all-empty one and returned [RET #true]), because
    [appendEntry] was widened to arbitrary [EntryNormal] proposals and has
    a reachable drop path.  The result is a bare [ok : bool]: the exact
    reject condition reads [r.uncommittedSize] and
    [r.maxUncommittedSize], neither of which [nstate.t] holds, so it cannot
    be stated against [own_raft_phys]; what *can* be stated is the
    empty-batch implication above.  On either path the struct is at the
    same [s]: the accept path writes [uncommittedSize := old + payloads],
    a field [own_raft_phys] does not pin, and the reject path writes
    nothing.

    Stated against [own_raft_phys] and the batch, which is all the body
    touches ([uncommittedSize], [maxUncommittedSize], and [payloadsSize]'s
    read of the slice).  The new [uncommittedSize] is not named because no
    predicate in this development mentions the field. *)
Definition wp_raft__increaseUncommittedSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (es : slice.t)
    (ents : list raftpb.Entry.t) (dq : dfrac),
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hes" ∷ es ↦*{dq} ents }}}
    r @! (go.PointerType raft.raft) @! "increaseUncommittedSize" #es
  {{{ (ok : bool), RET #ok;
      own_raft_phys cfg r id s ∗ es ↦*{dq} ents ∗
      (* an all-empty batch is never rejected *)
      ⌜ Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) ents →
        ok = true ⌝ }}}.

Module Type RAFT__INCREASEUNCOMMITTEDSIZE.
  Parameter wp_raft__increaseUncommittedSize :
    wp_raft__increaseUncommittedSize_body.
  Arguments wp_raft__increaseUncommittedSize {_ _ _ _ _ _ _ _}.
End RAFT__INCREASEUNCOMMITTEDSIZE.
