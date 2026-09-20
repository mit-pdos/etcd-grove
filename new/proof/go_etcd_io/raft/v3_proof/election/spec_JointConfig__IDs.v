Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** The ids of the voters, in some order, as [campaign] enumerates them.
    [campaign] calls this on [&r.trk.Config.Voters], so the receiver is that
    field ref and not the tracker itself.

    **In scope.  The translation defect that blocked this is fixed**
    (2026-09-17); what is left is ordinary proof work.

    Until 2026-09-17 Goose emitted the element read [c[0]] inside
    [JointConfig.IDs] as

        ![MajorityConfig] (IndexRef JointConfig (![JointConfig] "c", #(W64 0)))

    -- it *loaded* the operand and then asked [IndexRef] for a reference into
    the loaded **value**.  That is right for slices and wrong for arrays:

    - [index_ref_slice] ([new/golang/defn/slice.v:122]) takes [(#s, #i)] with
      [s : slice.t], a *value* -- a slice value carries [slice.ptr], so an
      address can be recovered from it;
    - [index_ref_array] ([new/golang/defn/array.v:50]) takes [(#l, #i)] with
      [l : loc], a *location* -- an [array.t V n] is [array.mk n (list V)]
      ([src/goose_lang/lang.v:528]) and carries no address at all, so there is
      nothing to take a reference into.

    So the body was **stuck** there and no Hoare triple about it was provable.
    The fix was in Goose ([goose/goose.go], [exprAddr]'s [*ast.IndexExpr]
    case): for an array operand take the array's address rather than loading
    it.  The emitted code is now

        ![MajorityConfig] (IndexRef JointConfig ("c", #(W64 0)))

    ([new/code/go_etcd_io/raft/v3/quorum.v:82], and :94 for [c[1]]), and the
    operand is exactly what the receiver's [GoAlloc JointConfig] produces, so
    [index_ref_array] applies.  Measured: the last [wp_auto] of the banked
    prefix in [proof_JointConfig__IDs.v] now steps the [IndexRef] to
    [#(array_index_ref map.t 0 c_ptr)] and stops at the *load* of that
    location -- an ownership obligation, not a missing rule.

    **What is left.**  Split element 0 out of ["c" : c_ptr ↦ ...Voters'] with
    [array_acc] ([new/golang/theory/array.v]); [Hvoters_arr] says the element
    is [voters_ref], so the load yields it.  Then a [wp_map_for_range] over
    [voters_ref] (the [Hvoters_dom] conjunct of [own_tracker] gives
    [dom voters = cfg]), then the same at index 1, where the element is
    [map.nil] and the pure step [wp_map_nil_for_range]
    ([new/golang/theory/map.v]) applies, then [return: m].  The statement
    here is the right one; do not weaken it.

    [slices.Sort] is *not* involved -- that sort is in [campaign], not in
    [IDs].

    [wp_JointConfig__CommittedIndex] ([v3_proof/readonly.v:718]) is still an
    [Axiom] for what *was* this same defect: [JointConfig.CommittedIndex]
    indexes the same array the same way (quorum.v:132,136).  It is now
    unblocked too and should be discharged. *)
Definition wp_JointConfig__IDs_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64),
  ∀ (trk : loc) tv votes,
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      trk ↦ tv ∗ own_tracker cfg tv votes ∗
      mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.

Module Type JOINTCONFIG__IDS.
  Parameter wp_JointConfig__IDs : wp_JointConfig__IDs_body.
  Arguments wp_JointConfig__IDs {_ _ _ _ _ _ _ _}.
End JOINTCONFIG__IDS.
