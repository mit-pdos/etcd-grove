Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [in.Full()] -- no more messages may be dispatched
    ([Inflights__Fullⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:201):

      in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)

    The answer is [inflights_full i] ([defs.v]), a function of the
    record -- which is why [own_Inflights] is indexed by one that
    determines it.  The point is not this triple but [Inflights.Add], which *panics*
    unless [Full()] is false; stating [Add] truthfully needs a name for
    "not full" that a caller can carry from the test to the use, and this is
    it. *)
Definition wp_Inflights__Full_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (i : inflights.t),
  {{{ is_pkg_init tracker ∗ "Hin" ∷ own_Inflights l i }}}
    l @! (go.PointerType tracker.Inflights) @! "Full" #()
  {{{ RET #(inflights_full i); own_Inflights l i }}}.

Module Type INFLIGHTS__FULL.
  Parameter wp_Inflights__Full : wp_Inflights__Full_body.
  Arguments wp_Inflights__Full {_ _ _ _ _ _ _ _}.
End INFLIGHTS__FULL.
