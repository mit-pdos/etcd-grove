Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [in.FreeLE(to)] frees the in-flight messages with index [<= to]
    ([Inflights__FreeLEⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:161;
    inflights.go:98):

        if in.count == 0 || to < in.buffer[in.start].index {
          return                                     // exit 1
        }
        idx := in.start
        var i int; var bytes uint64
        for i = 0; i < in.count; i++ {
          if to < in.buffer[idx].index { break }
          bytes += in.buffer[idx].bytes
          size := in.size
          if idx++; idx >= size { idx -= size }
        }
        in.count -= i
        in.bytes -= bytes
        in.start = idx
        if in.count == 0 { in.start = 0 }
        return                                       // exit 2

    **Panics**: none of its own; the two slice reads [in.buffer[in.start]]
    and [in.buffer[idx]] would panic out of range, and are in range by
    [inflights_ok] ([own_inflights]'s invariant): every occupied slot
    [start, start+count) (mod [size]) lies inside the buffer.  The [||]
    short-circuits, so [in.buffer[in.start]] is read only when
    [count > 0].  No call.

    The postcondition is what downstream needs: the ring stays well-formed
    ([own_inflights] at the new value, whose [inflights_ok] is the
    invariant), the buffer and its contents are untouched, [size],
    [maxBytes] and the buffer pointer are unchanged, and the occupancy does
    not grow.  [bytes] is **not** bounded: [in.bytes -= bytes] is
    [uint64] arithmetic and nothing relates [in.bytes] to the sizes in the
    buffer, so the subtraction can wrap; hence [Full()] is *not* claimed to
    become false here -- only [count' ≤ count]. *)
Definition wp_Inflights__FreeLE_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (iv : tracker.Inflights.t) (buf : list tracker.inflight.t)
    (to : w64),
  {{{ is_pkg_init tracker ∗ "Hin" ∷ own_inflights l iv buf }}}
    l @! (go.PointerType tracker.Inflights) @! "FreeLE" #to
  {{{ (iv' : tracker.Inflights.t), RET #();
      own_inflights l iv' buf ∗
      ⌜ iv'.(tracker.Inflights.size') = iv.(tracker.Inflights.size') ∧
        iv'.(tracker.Inflights.maxBytes') = iv.(tracker.Inflights.maxBytes') ∧
        iv'.(tracker.Inflights.buffer') = iv.(tracker.Inflights.buffer') ∧
        sint.Z iv'.(tracker.Inflights.count') ≤ sint.Z iv.(tracker.Inflights.count') ⌝ }}}.

Module Type INFLIGHTS__FREELE.
  Parameter wp_Inflights__FreeLE : wp_Inflights__FreeLE_body.
  Arguments wp_Inflights__FreeLE {_ _ _ _ _ _ _ _}.
End INFLIGHTS__FREELE.
