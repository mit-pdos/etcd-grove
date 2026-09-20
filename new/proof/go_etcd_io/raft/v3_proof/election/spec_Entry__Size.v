Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [Entry.Size()] (pointer receiver): the protobuf-encoded size of an entry.

    **Not translated.**  [new/code/go_etcd_io/raft/v3/raftpb.v] carries only
    the message types, the enum constants and the field accessors; the
    gogoproto-generated marshalling code ([Size], [Marshal], [Unmarshal],
    ...) is not in the translated set, so [raftpb.Assumptions] has no
    [MethodUnfold] for [Size] and the call cannot be stepped.  This axiom
    stands in for it, exactly as [spec_slices_Sort.v] does for [slices.Sort].

    It is reached on the election path: [raftLog.slice] applies
    [limitSize] to every page it returns and [limitSize] calls
    [ents[0].Size()] on any non-empty input ([v3.v:7497]), so
    [hasUnappliedConfChanges]'s [scan] hits it whenever
    [applied < committed].

    The postcondition says **nothing about the value**: [limitSize] and
    [entsSize] only use the sizes to decide where to cut a page, and no
    caller on this path depends on where the cut falls -- [scan] pages until
    [lo] reaches [hi] whatever the page sizes are.  So this is the weakest
    triple that lets the call be stepped: it owns the receiver (the method
    reads every field through the pointer) and hands it back.

    To discharge it: add [raftpb]'s [Size] methods to the translated set in
    [new/etc/update-goose-new.py], regenerate, and prove it from the body. *)
Definition wp_Entry__Size_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (e : loc) (dq : dfrac) (ev : raftpb.Entry.t),
  {{{ e ↦{dq} ev }}}
    e @! (go.PointerType raftpb.Entry) @! "Size" #()
  {{{ (n : w64), RET #n; e ↦{dq} ev }}}.

Module Type ENTRY__SIZE.
  Parameter wp_Entry__Size : wp_Entry__Size_body.
  Arguments wp_Entry__Size {_ _ _ _ _ _ _ _}.
End ENTRY__SIZE.
