Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [payloadsSize(ents)]: the summed payload size of the entries
    ([payloadsSizeⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:7524) -- a
    [slice.for_range] accumulating [payloadSize(e)], exactly [entsSize]'s
    shape.

    The result is **not** pinned to the sum of the [len(e.Data)]: that sum is
    computed in [uint64] with no overflow check, so a triple stating it would
    have to carry a bound premise that nothing on the election path can
    supply.  What is pinned is the case the callers care about -- a batch of
    empty payloads weighs [0].

    [increaseUncommittedSize], reached from [appendEntry], is called on the
    new leader's single empty [EntryNormal] and uses that implication.
    [maybeSendAppend] is the other caller and does not: it passes the result
    straight to [Progress.SentEntries], which forwards it to
    [Inflights.Add]'s [bytes] field, which nothing reads back.  The
    unconditional half of the postcondition (an unspecified [n]) exists for
    it -- the entries it weighs come out of the log and may carry data.
    Widened from the [Forall]-premised form on 2026-09-20; the old
    conclusion is the new implication applied to the old premise. *)
Definition wp_payloadsSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac),
  {{{ is_pkg_init raft ∗ "Hs" ∷ s ↦*{dq} es }}}
    @! raft.payloadsSize #s
  {{{ (n : w64), RET #n;
      s ↦*{dq} es ∗
      ⌜ Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) es →
        n = W64 0 ⌝ }}}.

Module Type PAYLOADSSIZE.
  Parameter wp_payloadsSize : wp_payloadsSize_body.
  Arguments wp_payloadsSize {_ _ _ _ _ _ _ _}.
End PAYLOADSSIZE.
