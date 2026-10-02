Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** ** The [unstable] suffix

    Three [maybe*] methods, all on a bare [*unstable] so they can be reused
    wherever the field is split out.  Each takes the pending snapshot's
    pointer as [own_snap uv.snapshot snap] ([inv_raftlog.v]): [None] is
    [snapshot = nil], [Some sid] a pending snapshot whose metadata is [sid]
    (since 2026-10-02; until then [snapshot = nil] was a premise and the
    snapshot arms were dead).

    [u.maybeFirstIndex()]: [snapshot.Metadata.Index + 1] when a snapshot is
    pending, and [ok = false] otherwise. *)
Definition wp_unstable__maybeFirstIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t) (uents : list raftpb.Entry.t)
    (snap : option raft.entryID.t),
  {{{ is_pkg_init raft ∗ "Hun" ∷ own_unstable u uv uents ∗
      "#Hsnap" ∷ own_snap uv.(raft.unstable.snapshot') snap }}}
    u @! (go.PointerType raft.unstable) @! "maybeFirstIndex" #()
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      own_unstable u uv uents ∗
      ⌜ ok = bool_decide (snap ≠ None) ∧
        ∀ sid, snap = Some sid → i = word.add sid.(raft.entryID.index') (W64 1) ⌝ }}}.

Module Type UNSTABLE__MAYBEFIRSTINDEX.
  Parameter wp_unstable__maybeFirstIndex : wp_unstable__maybeFirstIndex_body.
  Arguments wp_unstable__maybeFirstIndex {_ _ _ _ _ _ _ _}.
End UNSTABLE__MAYBEFIRSTINDEX.
