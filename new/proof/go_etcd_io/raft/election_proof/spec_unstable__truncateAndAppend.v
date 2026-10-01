Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.truncateAndAppend(ents)]: splice a non-empty batch into the unstable
    suffix ([unstable__truncateAndAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1650).

    The body switches on where the batch starts, [fromIndex = ents[0].Index]:

      1. [fromIndex == u.offset+len(u.entries)]: it continues the suffix,
         [u.entries = append(u.entries, ents...)];
      2. [fromIndex <= u.offset]: [Infof], then the suffix is *replaced*:
         [u.entries = ents], [u.offset = fromIndex],
         [u.offsetInProgress = u.offset];
      3. otherwise: [Infof], then [keep := u.slice(u.offset, fromIndex)],
         [u.entries = append(keep, ents...)],
         [u.offsetInProgress = min(u.offsetInProgress, fromIndex)].

    All three are specified (since 2026-10-01; before, only arm 1).  One
    statement covers them: the new suffix is
    [take (fromIndex - u.offset) uents ++ ents] ([take 0] in arm 2, where
    the difference is [<= 0]; [take len] in arm 1) and the new offset is
    [fromIndex] if that is below [u.offset], else [u.offset].  The premise
    [fromIndex <= u.offset + len] is what keeps arm 3's [u.slice] inside
    the suffix (its [mustCheckOutOfBounds] [Panicf]s otherwise); the
    no-wrap premise is [u.slice]'s.  [u.logger] is a [Logger] for the two
    [Infof]s.

    **Ownership of the batch.**  Arms 1 and 3 copy the entry values
    ([append]), so the batch is lent and comes back.  Arm 2 *adopts the
    caller's slice*: [u.entries] then aliases it, and a later arm-1
    [append] may write into its capacity slack
    (notes/raft-implementation-facts.md, "Which slices raft hands out
    uncapped").  So in that arm -- exactly when [fromIndex <= u.offset] and
    the batch does not continue the suffix -- the caller must hand the
    batch over read-only ([dq = DfracDiscarded]) together with its
    capacity, and gets nothing back.  The condition is computed in the
    spec, so a caller that knows its batch continues the suffix
    ([appendEntry]) owes nothing extra.

    The new [unstable] value is existential, with the three fields
    [own_raftLog] tracks pinned: [offset] as above, [snapshot] and
    [logger] unchanged.  [offsetInProgress] is not tracked by anything. *)
Definition wp_unstable__truncateAndAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t) (uents ents : list raftpb.Entry.t)
    (e0 : raftpb.Entry.t) (es : slice.t) (dq : dfrac) (ulg : interface.t_ok),
  ents !! 0%nat = Some e0 →
  (uint.Z e0.(raftpb.Entry.Index')
   ≤ uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  uv.(raft.unstable.logger') = interface.ok ulg →
  {{{ is_pkg_init raft ∗
      "Hun" ∷ own_unstable u uv uents ∗
      "Hes" ∷ es ↦*{dq} ents ∗
      "#Hlg" ∷ is_Logger ulg ∗
      "Hadopt" ∷ (if bool_decide ((uint.Z e0.(raftpb.Entry.Index') ≤ uint.Z uv.(raft.unstable.offset'))%Z ∧
                                  (uint.Z e0.(raftpb.Entry.Index')
                                   ≠ uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z)%type
                  then ⌜ dq = DfracDiscarded ⌝ ∗ own_slice_cap raftpb.Entry.t es (DfracOwn 1)
                  else True) }}}
    u @! (go.PointerType raft.unstable) @! "truncateAndAppend" #es
  {{{ (uv' : raft.unstable.t), RET #();
      own_unstable u uv'
        (take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z uv.(raft.unstable.offset')))
           uents ++ ents) ∗
      ⌜ uint.Z uv'.(raft.unstable.offset') =
          (uint.Z e0.(raftpb.Entry.Index') `min` uint.Z uv.(raft.unstable.offset'))%Z ∧
        uv'.(raft.unstable.snapshot') = uv.(raft.unstable.snapshot') ∧
        uv'.(raft.unstable.logger') = uv.(raft.unstable.logger') ⌝ ∗
      (if bool_decide ((uint.Z e0.(raftpb.Entry.Index') ≤ uint.Z uv.(raft.unstable.offset'))%Z ∧
                       (uint.Z e0.(raftpb.Entry.Index')
                        ≠ uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z)%type
       then True else es ↦*{dq} ents) }}}.

Module Type UNSTABLE__TRUNCATEANDAPPEND.
  Parameter wp_unstable__truncateAndAppend :
    wp_unstable__truncateAndAppend_body.
  Arguments wp_unstable__truncateAndAppend {_ _ _ _ _ _ _ _}.
End UNSTABLE__TRUNCATEANDAPPEND.
