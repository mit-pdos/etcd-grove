Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** **This statement was FALSE until 2026-09-16** and is now repaired.  The
    repair is recorded here rather than silently applied, because a [Qed]
    resting on a false [Admitted] is unsound and [proof_raft__reset.v] --
    hence [becomeFollower], [becomeCandidate], [becomeLeader] and everything
    above them -- was resting on this one.

    **What was wrong.**  The precondition owned no part of the tracker
    *struct*.  [own_tracker tv votes] is indexed by the tracker *value* and
    owns what that value points at -- the vote map, the progress map, the id
    sets -- not the bytes of [trk] itself.  But [Visit] has a pointer
    receiver and its very first statement is [n := len(p.Progress)], which
    Goose translates to

        ![tracker.ProgressMap]
          (StructFieldRef ProgressTracker "Progress"
             (![go.PointerType ProgressTracker] "p"))

    -- a load through [trk.[ProgressTracker.t, "Progress"]]
    ([new/code/go_etcd_io/raft/v3/tracker.v:809]).  It reads that field again
    inside the second range, for the [map.lookup1] that produces each [pr]
    ([tracker.v:837]).  So the triple asserted safety of a load from a
    location it did not own.  Measured with two probes, each
    [rocq compile -vok] RC=0:

      - precondition as it was: [wp_start; iNamed "Hown"; wp_auto] parks
        immediately, with the whole body still to run;
      - precondition plus [trk ↦ tv]: the same three tactics get through the
        receiver alloc, the field load and the [len] call's argument.

    The comment that used to sit here claimed "[Visit] reads the progress map
    out of the tracker value it is given and does not mutate the tracker
    itself, so it does not need the location".  The second half is true and
    the first is not -- it reads the map *reference* out of the struct,
    through the pointer.  Mutation was never the question; any read through
    the receiver is.  An invariant promised in prose and absent from the
    conjuncts, which is the same failure as the [r.step] one; see
    notes/STATUS.md's table.

    **The repair**, applied: [trk ↦ tv] in the pre- and postcondition, and
    lent to the closure as well ([visit_closure trk tv f I],
    [inv_tracker.v]).  Lending
    is necessary, not cosmetic -- see that definition's comment.
    [proof_raft__reset.v] keeps the field split out with its
    [raft_split_trk] instead of re-assembling it after [ResetVotes], and its
    closure applies the continuation wand to read [r.trk.MaxInflight] and
    re-splits before returning.

    **The statement is now true, and the two tooling obstacles that blocked
    it are fixed** (2026-09-17).  Both were unrelated to raft:

    1. [var sl [7]uint64; if len(sl) >= n] asks for [len] of an *array*.
       There was **no** [FuncUnfold go.len [go.ArrayType n t]] instance
       anywhere under [new/golang/] ([go.len_underlying] does not help: an
       array type is already its own underlying type), *and* Goose emitted
       [FuncResolve go.len [go.ArrayType 7 go.uint64] #()] with no operand
       applied -- a function value used as an integer.  Goose now folds the
       constant, so the code reads [#(W64 7) >=⟨go.int⟩ ![go.int] "n"]
       ([tracker.v:814]), and [go.len_array] / [pure_wp_array_len] cover the
       non-constant case.  (Contrast maps, where the instance exists but only
       at the literal [go.MapType]; [wp_ProgressMap_len] in [inv_tracker.v]
       is that workaround.)
    2. [ids = sl[:n]] was translated as [Slice] applied to the array *value*,
       where [slice_array_step] ([new/golang/defn/array.v]) steps only on an
       array *location*.  Goose now passes the address:
       [let: "$s" := "sl" in Slice (go.ArrayType 7 go.uint64) ("$s", #(W64 0),
       ![go.int] "n")] ([tracker.v:816-817]).  This was also a *semantic* fix
       independent of the model -- in Go [sl[:n]] aliases [sl], and a slice of
       a copy does not.

    The [else] branch ([make([]uint64, n)], taken when [size cfg > 7]) was
    always fine.

    Nothing about the *proof* is hard once the code steps: a
    [wp_map_for_range] filling [ids] backwards from [n-1], [wp_slices_Sort]
    ([spec_slices_Sort.v]) for the permutation, then a [slice.for_range] applying
    [visit_closure] to each id with [big_sepM_lookup_acc] on [Hprogs].  The
    sorted order is not observable -- no caller's [I] mentions it -- so the
    permutation-only postcondition of [wp_slices_Sort] is enough. *)
Definition wp_ProgressTracker__Visit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes (f : func.t) (I : iProp Σ),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv votes ∗ I ∗
      □ visit_closure trk tv f I }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "Visit" #f
  {{{ RET #(); trk ↦ tv ∗ own_tracker cfg tv votes ∗ I }}}.

Module Type PROGRESSTRACKER__VISIT.
  Parameter wp_ProgressTracker__Visit : wp_ProgressTracker__Visit_body.
  Arguments wp_ProgressTracker__Visit {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__VISIT.
