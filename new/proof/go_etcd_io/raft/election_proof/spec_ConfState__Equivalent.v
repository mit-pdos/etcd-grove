Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [cs1.Equivalent(cs2)] ([raftpb/confstate.go]) returns [nil] iff the two
    [ConfState]s are [reflect.DeepEqual] after each of their four id slices
    has been copied with [append([]uint64(nil), s...)] and sorted.

    **Not translated** ([raftpb] is types-only), so this is an [Axiom].  It
    is stated for the voters-only case [newRaft] needs: both sides have
    empty [VotersOutgoing], [Learners] and [LearnersNext], equal
    [AutoLeave], and [Voters] lists that are permutations of each other.
    Then every slice sorts to the same list -- the empty ones to [nil],
    whether they started [nil] or empty, because [append] of nothing to
    [nil] is [nil] -- and [ConfState] has exactly these five fields
    ([raftpb/raft.pb.go]), so [DeepEqual] holds and the result is [nil].

    Only the [nil] outcome is specified: the one caller,
    [assertConfStatesEquivalent], [Panic]s on anything else. *)
Definition wp_ConfState__Equivalent_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (p : loc) (cs1 cs2 : raftpb.ConfState.t) (v1 v2 : list w64) (dq1 dq2 : dfrac),
  v1 ≡ₚ v2 →
  cs1.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 →
  cs1.(raftpb.ConfState.Learners').(slice.len) = W64 0 →
  cs1.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 →
  cs2.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 →
  cs2.(raftpb.ConfState.Learners').(slice.len) = W64 0 →
  cs2.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 →
  cs1.(raftpb.ConfState.AutoLeave') = cs2.(raftpb.ConfState.AutoLeave') →
  {{{ is_pkg_init raftpb ∗ p ↦ cs1 ∗
      cs1.(raftpb.ConfState.Voters') ↦*{dq1} v1 ∗
      cs2.(raftpb.ConfState.Voters') ↦*{dq2} v2 }}}
    p @! (go.PointerType raftpb.ConfState) @! "Equivalent" #cs2
  {{{ RET #interface.nil;
      p ↦ cs1 ∗
      cs1.(raftpb.ConfState.Voters') ↦*{dq1} v1 ∗
      cs2.(raftpb.ConfState.Voters') ↦*{dq2} v2 }}}.

Module Type CONFSTATE__EQUIVALENT.
  Parameter wp_ConfState__Equivalent : wp_ConfState__Equivalent_body.
  Arguments wp_ConfState__Equivalent {_ _ _ _ _ _ _ _}.
End CONFSTATE__EQUIVALENT.
