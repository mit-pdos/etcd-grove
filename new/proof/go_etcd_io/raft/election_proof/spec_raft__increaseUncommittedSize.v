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
    budget holds, the reject path is **unreachable**, and the field is
    incremented by zero.  That is the fact [appendEntry] needs to show its
    own [return false] -- and hence [becomeLeader]'s [logger.Panic] -- is
    dead code.  Like [payloadsSize], it is stated only for the empty-payload
    case; the general statement would have to talk about the budget
    arithmetic, which no caller on the election path exercises.

    Stated against the bare struct points-to rather than [own_raft_phys],
    for two reasons.  It is the minimal ownership the body needs (it touches
    [uncommittedSize] and [maxUncommittedSize] and nothing else), and
    [appendEntry] calls this *between* two [raftLog] calls that are stated
    at a fixed log split -- re-sealing [own_raft_phys] across it would
    existentially re-quantify the split and lose the last index it just
    read.  The new [uncommittedSize] is existential because the value
    written, [old + payloadsSize(ents)], is not worth naming: no predicate
    in this development mentions the field. *)
Definition wp_raft__increaseUncommittedSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (es : slice.t)
    (ents : list raftpb.Entry.t) (dq : dfrac),
  Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) ents →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hes" ∷ es ↦*{dq} ents }}}
    r @! (go.PointerType raft.raft) @! "increaseUncommittedSize" #es
  {{{ RET #true; own_raft_phys cfg r id s ∗ es ↦*{dq} ents }}}.

Module Type RAFT__INCREASEUNCOMMITTEDSIZE.
  Parameter wp_raft__increaseUncommittedSize :
    wp_raft__increaseUncommittedSize_body.
  Arguments wp_raft__increaseUncommittedSize {_ _ _ _ _ _ _ _}.
End RAFT__INCREASEUNCOMMITTEDSIZE.
