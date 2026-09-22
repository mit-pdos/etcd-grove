Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [in.Add(index, bytes)] records one dispatched message
    ([Inflights__Addⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:95).

    Two things make the premise necessary rather than convenient.

    1. The body opens with [if in.Full() { panic("cannot add into a Full
       inflights") }].  A triple without [inflights_full iv = false] would
       be false, not merely weak.
    2. It then writes [in.buffer[(in.start+in.count) mod in.size]], growing
       the buffer on demand.  That the slot is in range is the content of
       [inflights_ok] in [own_inflights_at] ([inv_tracker.v]); without it the
       triple is *also* false (start = 100, count = 0, size = 1000, empty
       buffer is not [Full], grows to one slot and indexes slot 100).

    The resulting [Inflights] value is existential: nothing on the election
    path reads the window back.  [SentEntries] immediately re-tests [Full()],
    and stores the answer in [MsgAppFlowPaused], which only [IsPaused]
    reads -- and either answer there is fine. *)
Definition wp_Inflights__Add_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (iv : tracker.Inflights.t) (index bytes : w64),
  inflights_full iv = false →
  {{{ is_pkg_init tracker ∗ "Hin" ∷ own_inflights_at l iv }}}
    l @! (go.PointerType tracker.Inflights) @! "Add" #index #bytes
  {{{ RET #(); own_inflights l }}}.

Module Type INFLIGHTS__ADD.
  Parameter wp_Inflights__Add : wp_Inflights__Add_body.
  Arguments wp_Inflights__Add {_ _ _ _ _ _ _ _}.
End INFLIGHTS__ADD.
