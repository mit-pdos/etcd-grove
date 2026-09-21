Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [in.grow()] doubles the ring buffer, capped at [in.size]
    ([Inflights__growⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:131):

      newSize := len(in.buffer) * 2
      if newSize == 0 { newSize = 1 } else if newSize > in.size { newSize = in.size }
      newBuffer := make([]inflight, newSize)
      copy(newBuffer, in.buffer)
      in.buffer = newBuffer

    Stated over the *pieces* of [own_inflights_at] rather than over the
    predicate itself, because the premise and the conclusion are both about
    the **length of the buffer**, which [own_inflights_at] hides.  The only
    caller is [Inflights.Add], which holds the pieces open anyway.

    The premise [len(buffer) < size] is the "grow on demand" contract, and it
    is necessary rather than convenient: with [size = 0] (hence
    [len(buffer) = 0], by [inflights_ok]) the code takes the [newSize == 0]
    branch and allocates **one** slot, i.e. a buffer longer than the ring,
    breaking [0 ≤ len(buffer) ≤ size].  The [size < 2^62] premise -- also an
    [inflights_ok] conjunct -- is what keeps [len(buffer) * 2] from
    overflowing [go.int].

    Both premises together give [size ≥ 1], so the new length is
    [max 1 (min (2 * len(buffer)) size)]; in particular it is *strictly*
    greater than the old one, which is what [Add] needs in order to know that
    the slot it is about to write is now in range. *)
Definition wp_Inflights__grow_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (iv : tracker.Inflights.t) (buf : list tracker.inflight.t),
  (Z.of_nat (length buf) < sint.Z iv.(tracker.Inflights.size'))%Z →
  (sint.Z iv.(tracker.Inflights.size') < 2 ^ 62)%Z →
  {{{ is_pkg_init tracker ∗
      "Hiv" ∷ l ↦ iv ∗
      "Hbuf" ∷ iv.(tracker.Inflights.buffer') ↦* buf ∗
      "Hbuf_cap" ∷ own_slice_cap tracker.inflight.t
                     iv.(tracker.Inflights.buffer') (DfracOwn 1) }}}
    l @! (go.PointerType tracker.Inflights) @! "grow" #()
  {{{ (sl : slice.t) (buf' : list tracker.inflight.t), RET #();
      "Hiv" ∷ l ↦ (iv <| tracker.Inflights.buffer' := sl |>) ∗
      "Hbuf" ∷ sl ↦* buf' ∗
      "Hbuf_cap" ∷ own_slice_cap tracker.inflight.t sl (DfracOwn 1) ∗
      "%Hlen" ∷ ⌜ Z.of_nat (length buf')
                  = Z.max 1 (Z.min (2 * Z.of_nat (length buf))
                                   (sint.Z iv.(tracker.Inflights.size'))) ⌝ ∗
      "%Hcontents" ∷ ⌜ buf' = buf ++ replicate (length buf' - length buf)
                                       (zero_val tracker.inflight.t) ⌝ }}}.

Module Type INFLIGHTS__GROW.
  Parameter wp_Inflights__grow : wp_Inflights__grow_body.
  Arguments wp_Inflights__grow {_ _ _ _ _ _ _ _}.
End INFLIGHTS__GROW.
