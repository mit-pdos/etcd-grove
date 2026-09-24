Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [assertConfStatesEquivalent l cs1 cs2] returns iff [cs1.Equivalent(cs2)]
    is [nil], and otherwise calls [l.Panic].  Stated for the voters-only
    case [ConfState.Equivalent]'s triple covers
    ([spec_ConfState__Equivalent.v]); the [Panic] path is then unreachable,
    which is why the logger needs no contract here. *)
Definition wp_assertConfStatesEquivalent_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : raft.Logger.t) (cs1 cs2 : raftpb.ConfState.t) (v1 v2 : list w64)
    (dq1 dq2 : dfrac),
  v1 ≡ₚ v2 →
  cs1.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 →
  cs1.(raftpb.ConfState.Learners').(slice.len) = W64 0 →
  cs1.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 →
  cs2.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 →
  cs2.(raftpb.ConfState.Learners').(slice.len) = W64 0 →
  cs2.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 →
  cs1.(raftpb.ConfState.AutoLeave') = cs2.(raftpb.ConfState.AutoLeave') →
  {{{ is_pkg_init raft ∗
      cs1.(raftpb.ConfState.Voters') ↦*{dq1} v1 ∗
      cs2.(raftpb.ConfState.Voters') ↦*{dq2} v2 }}}
    @! raft.assertConfStatesEquivalent #l #cs1 #cs2
  {{{ RET #();
      cs1.(raftpb.ConfState.Voters') ↦*{dq1} v1 ∗
      cs2.(raftpb.ConfState.Voters') ↦*{dq2} v2 }}}.

Module Type ASSERTCONFSTATESEQUIVALENT.
  Parameter wp_assertConfStatesEquivalent : wp_assertConfStatesEquivalent_body.
  Arguments wp_assertConfStatesEquivalent {_ _ _ _ _ _ _ _}.
End ASSERTCONFSTATESEQUIVALENT.
