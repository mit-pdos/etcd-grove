Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** The ids of the voters, in some order, as [campaign] enumerates them.
    [campaign] calls this on [&r.trk.Config.Voters], so the receiver is that
    field ref and not the tracker itself.

    **In scope, and blocked on the *translation*, not on the proof**
    (2026-09-16).  This was an [Axiom] until today.  It is core raft, so under
    the scope rule it may not be assumed; it is now an [Admitted] [Lemma] with
    the machine-checked prefix in [proof_JointConfig__IDs.v] banked.  What blocks it is not anything
    about raft: it is a disagreement between what Goose emits for array
    indexing and what the model gives a step to.

    [quorum.JointConfig] is [[2]MajorityConfig], i.e. an **array**
    ([new/code/go_etcd_io/raft/v3/quorum.v:552]).  Goose translates the
    element read [c[0]] inside [JointConfig.IDs] (quorum.v:82, and again at
    :94 for [c[1]]) as

        ![MajorityConfig] (IndexRef JointConfig (![JointConfig] "c", #(W64 0)))

    -- it *loads* the operand and then asks [IndexRef] for a reference into
    the loaded **value**.  That is right for slices and wrong for arrays:

    - [index_ref_slice] ([new/golang/defn/slice.v:122]) takes [(#s, #i)] with
      [s : slice.t], a *value* -- a slice value carries [slice.ptr], so an
      address can be recovered from it;
    - [index_ref_array] ([new/golang/defn/array.v:50]) takes [(#l, #i)] with
      [l : loc], a *location* -- an [array.t V n] is [array.mk n (list V)]
      ([src/goose_lang/lang.v:528]) and carries no address at all, so there is
      nothing to take a reference into.

    So the translated body is **stuck** at that [IndexRef] and no Hoare triple
    about it is provable.  Measured, not inferred -- three one-line probes,
    each checked with [rocq compile -vok]:

        (* steps: goal becomes  Φ #(array_index_ref map.t (sint.Z 0) l)  *)
        Lemma probe_loc (l : loc) Φ :
          ⊢ WP (IndexRef quorum.JointConfig (#l, #(W64 0)))%E {{ Φ }}.
        Proof. iStartProof. wp_auto. Admitted.

        (* does NOT step: [wp_auto] reports "Failed to progress" *)
        Lemma probe_val (a : array.t loc 2) Φ :
          ⊢ WP (IndexRef quorum.JointConfig (#a, #(W64 0)))%E {{ Φ }}.
        Proof. iStartProof. wp_auto. Admitted.

        (* steps: goal becomes  WP match array.arr a !! 0 with ... end  *)
        Lemma probe_index_val (a : array.t loc 2) Φ :
          ⊢ WP (Index quorum.JointConfig (#a, #(W64 0)))%E {{ Φ }}.
        Proof. iStartProof. wp_auto. Admitted.

    i.e. Goose emits the one combination of operator and operand that has no
    rule.  Either of the other two would work, so the fix belongs in the Go
    fork's Goose and not here: for an addressable array operand emit
    [IndexRef T ("c", i)] (the address), or, since this occurrence is a plain
    read, emit the value form [Index T (![T] "c", i)], for which
    [index_array] ([new/golang/defn/array.v:54]) does have a rule.  With
    [Hvoters_arr] in hand the value form reduces straight to [voters_ref].

    Nothing else here is missing.  Once the operand steps, the remainder is
    a [wp_map_for_range] over [voters_ref] (the [Hvoters_dom] conjunct of
    [own_tracker] gives [dom voters = cfg]) followed by the pure step
    [wp_map_nil_for_range] ([new/golang/theory/map.v:305]) for the nil second
    component of the joint config, then [return: m].  The statement here is
    the right one; do not weaken it.

    The same defect is why [wp_JointConfig__CommittedIndex]
    ([v3_proof/readonly.v:718]) is an [Axiom]: [JointConfig.CommittedIndex]
    indexes the same array the same way (quorum.v:132,136). *)
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
