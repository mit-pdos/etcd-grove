Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [in.grow()] doubles the ring buffer, capped at [in.size]
    ([Inflights__growⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:131):

      newSize := len(in.buffer) * 2
      if newSize == 0 { newSize = 1 } else if newSize > in.size { newSize = in.size }
      newBuffer := make([]inflight, newSize)
      copy(newBuffer, in.buffer)
      in.buffer = newBuffer

    Stated on [own_inflights] at the exact buffer contents: the premise and
    the conclusion are both about the **length of the buffer**, which is why
    [own_inflights] is indexed by the buffer and not only by the value.
    (Until 2026-09-23 this was stated over the predicate's raw pieces.)  The
    only caller is [Inflights.Add].

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
  {{{ is_pkg_init tracker ∗ "Hin" ∷ own_inflights l iv buf }}}
    l @! (go.PointerType tracker.Inflights) @! "grow" #()
  {{{ (sl : slice.t) (buf' : list tracker.inflight.t), RET #();
      "Hin" ∷ own_inflights l (iv <| tracker.Inflights.buffer' := sl |>) buf' ∗
      "%Hlen" ∷ ⌜ Z.of_nat (length buf')
                  = Z.max 1 (Z.min (2 * Z.of_nat (length buf))
                                   (sint.Z iv.(tracker.Inflights.size'))) ⌝ ∗
      "%Hcontents" ∷ ⌜ buf' = buf ++ replicate (length buf' - length buf)
                                       (zero_val tracker.inflight.t) ⌝ }}}.

Module Type INFLIGHTS__GROW.
  Parameter wp_Inflights__grow : wp_Inflights__grow_body.
  Arguments wp_Inflights__grow {_ _ _ _ _ _ _ _}.
End INFLIGHTS__GROW.
