Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.truncateAndAppend(ents)]: splice a batch into the unstable suffix
    ([unstable__truncateAndAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1650).

    The body switches on where the batch starts, [fromIndex = ents[0].Index]:

      - [fromIndex == u.offset+len(u.entries)]: it continues the suffix, so
        [u.entries = append(u.entries, ents...)];
      - [fromIndex <= u.offset]: it replaces the suffix outright;
      - otherwise: keep [u.entries[:fromIndex]] and append.

    Only the first is specified, and the premise [Hcont] is exactly its
    guard.  That is not a weakening of what the function does: the other two
    arms truncate, and the only caller in this development is
    [raftLog.append], which is called from [appendEntry] with indices that
    continue the log by construction ([appendEntry] stamps
    [lastIndex()+1+i] into every entry before calling it).  Both other arms
    also start with an [Infof], which is fine, but they would need a spec
    saying which entries survive -- state it when a [MsgApp] path needs it.

    Ownership.  A pointer-receiver method that *writes* [u.entries] needs the
    receiver's fields ([notes/gotchas.md]), so [u ↦ uv] is here, and the
    suffix's own slice comes with its capacity: Go's [append] may reallocate,
    which is why the new slice value [sl] is existential in the
    postcondition and the struct comes back at [uv <| entries' := sl |>].
    The batch [es] is *lent* -- [append] copies the values -- so it is
    returned unchanged at the caller's fraction.

    No no-wrap premise is needed for the guard's [u.offset+len(u.entries)]:
    [Hcont] equates it with [uint.Z] of a [w64], so it is below [2^64]
    already. *)
Definition wp_unstable__truncateAndAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t) (uents ents : list raftpb.Entry.t)
    (e0 : raftpb.Entry.t) (es : slice.t) (dq : dfrac),
  ents !! 0%nat = Some e0 →
  (uint.Z e0.(raftpb.Entry.Index')
   = uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z →
  {{{ is_pkg_init raft ∗
      "Hun" ∷ own_unstable u uv uents ∗
      "Hes" ∷ es ↦*{dq} ents }}}
    u @! (go.PointerType raft.unstable) @! "truncateAndAppend" #es
  {{{ (sl : slice.t), RET #();
      own_unstable u (uv <| raft.unstable.entries' := sl |>) (uents ++ ents) ∗
      es ↦*{dq} ents }}}.

Module Type UNSTABLE__TRUNCATEANDAPPEND.
  Parameter wp_unstable__truncateAndAppend :
    wp_unstable__truncateAndAppend_body.
  Arguments wp_unstable__truncateAndAppend {_ _ _ _ _ _ _ _}.
End UNSTABLE__TRUNCATEANDAPPEND.
