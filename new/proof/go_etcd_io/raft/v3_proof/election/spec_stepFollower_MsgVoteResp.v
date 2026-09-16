Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [stepFollower] on a [MsgVoteResp]: nothing at all.

    [stepFollowerⁱᵐᵖˡ] ([new/code/go_etcd_io/raft/v3.v]) is a single type
    switch over [m.Type] with arms for [MsgProp], [MsgApp], [MsgHeartbeat],
    [MsgSnap], [MsgTransferLeader], [MsgForgetLeader], [MsgTimeoutNow],
    [MsgReadIndex] and [MsgReadIndexResp].  [MsgVoteResp] is none of those, so
    control falls off the end of the switch to the function's trailing
    [return nil] without reading or writing a single field of the raft struct.

    Hence: state completely unchanged, no message sent, [nil] error.  That is
    the whole content of the spec, and it is what makes [Step]'s [MsgVoteResp]
    branch refine [step_refl] when the receiver is a follower.

    No premise beyond the message type is needed.  In particular the role is
    not mentioned: the body never looks at [r.state], so the triple holds for
    any [s].  (A caller reaching this function through [r.step] does know
    [s.(nstate.role) = role.Follower], from [own_raft_phys]'s [Hstepfn]
    conjunct and [step_func_of]; it simply does not have to pass it on.) *)
Definition wp_stepFollower_MsgVoteResp_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgVoteResp →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    @! raft.stepFollower #r #m
  {{{ (err : error.t), RET #err;
      own_raft_phys cfg r id s ∗ ⌜ err = interface.nil ⌝ }}}.

Module Type STEPFOLLOWER.
  Parameter wp_stepFollower_MsgVoteResp : wp_stepFollower_MsgVoteResp_body.
  Arguments wp_stepFollower_MsgVoteResp {_ _ _ _ _ _ _ _}.
End STEPFOLLOWER.
