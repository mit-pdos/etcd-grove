Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_Config__validate.

(** * [newRaft]: the constructor of [own_raft_phys]

    This triple is the witness that [own_raft_phys] is **satisfiable** by a
    struct the Go code actually builds: from a [Config] and a [Storage] it
    produces [own_raft_phys cfg r id s] at a well-formed follower state.
    Every other spec in the development takes [own_raft_phys] as given; this
    is the one that establishes it.

    ** What it assumes, and why

    [newRaft] panics on several inputs, and its spec has to exclude each
    one.  The premises are, in order:

    - [config_valid cv] ([spec_Config__validate.v]): what [validate] checks,
      so [validate] returns [nil] -- plus a non-nil [Logger].
    - **[MaxInflightMsgs < 2^62]: not implied by [validate]**, which only
      checks [> 0].  [own_tracker]'s [HmaxInfl] ([inv_tracker.v]) demands it
      because [Inflights.grow] computes [len(buffer) * 2], which overflows a
      Go [int] once the buffer reaches [2^62].  So [own_raft_phys] is
      **unsatisfiable for a valid [Config] with [MaxInflightMsgs ≥ 2^62]**
      (found writing this spec, 2026-09-24).  Not a bug a real run can hit
      -- the buffer only grows to [2^62] with that many messages in flight
      -- but a gap between what raft accepts and what the proof covers.
    - the development's scope: [PreVote = CheckQuorum = false], and
      [DisableProposalForwarding = false] (a follower forwards proposals;
      since 2026-10-02, for [stepFollower]'s forwarding arm).
    - the storage's contents ([own_Storage (interface.ok si) prev ents]):
      contiguous indices and **no configuration-change entry**.  The second
      is [HnoConfChange]'s scope assumption and is false of a node
      [RawNode.Bootstrap] just bootstrapped (notes/STATUS.md).
    - [Storage.InitialState] returns [(hs, cs, nil)] and lends [cs.Voters].
      This is a premise, not a clause of [is_Storage]: it is a fact about
      one storage at one moment, and nothing else calls the method.
    - [hs.Commit] lies in [[prev.index, lastIndex]] unless [hs] is empty
      (else [loadState] panics), and [Applied] is [0] or lies in
      [[prev.index, committed]] (else [appliedTo] panics).
    - the [ConfState] is **voters-only**, with a non-empty list of
      **distinct, non-zero** voters.  Each clause is needed:
      learners/joint configurations are out of scope; [Restore] skips a
      zero id and de-duplicates, after which [assertConfStatesEquivalent]
      panics; and an empty voter set is what a node joining an existing
      cluster starts with (etcd's [StartNode] with no peers), which
      [own_tracker]'s [Hcfg_ne] excludes -- so **such a node is outside the
      development** until it receives a snapshot, which is out of scope too.

    ** What it gives

    [own_raft_phys] over the voter set, at a state that is [nstate_wf]
    (ready for [Step]), a follower with no leader, an empty tally and an
    empty outbox, whose [term] and [vote] are the persisted [HardState]'s.
    For a fresh storage ([hs] empty) that is [nstate_rel s init_pstate]
    ([newRaft_post_init], [election.v]): the struct [newRaft] builds refines the
    protocol state [own_raft_ghost_alloc] starts every node in. *)
Section defs.
Context {ext : ffi_syntax}.

Definition hs_empty (hs : raftpb.HardState.t) : Prop :=
  hs.(raftpb.HardState.Term') = W64 0 ∧ hs.(raftpb.HardState.Vote') = W64 0 ∧
  hs.(raftpb.HardState.Commit') = W64 0.

(** [raftLog.committed] after [newRaft]'s [loadState] (skipped for an empty
    [HardState]). *)
Definition committed_after (prev : raft.entryID.t) (hs : raftpb.HardState.t) : w64 :=
  if bool_decide (hs_empty hs) then prev.(raft.entryID.index')
  else hs.(raftpb.HardState.Commit').

End defs.

Definition wp_newRaft_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (c : loc) (cv : raft.Config.t) (lok si : interface.t_ok)
    (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (hs : raftpb.HardState.t) (cs : raftpb.ConfState.t)
    (voters : list w64) (dqv : dfrac),
  (* the Config *)
  config_valid cv →
  cv.(raft.Config.Logger') = interface.ok lok →
  cv.(raft.Config.Storage') = interface.ok si →
  (sint.Z cv.(raft.Config.MaxInflightMsgs') < 2 ^ 62)%Z →
  cv.(raft.Config.PreVote') = false →
  cv.(raft.Config.CheckQuorum') = false →
  cv.(raft.Config.DisableProposalForwarding') = false →
  (* the stored log *)
  log_indices_ok prev ents →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (* the persisted HardState *)
  (¬ hs_empty hs →
   uint.Z prev.(raft.entryID.index') ≤ uint.Z hs.(raftpb.HardState.Commit')
     ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents))%Z →
  (cv.(raft.Config.Applied') = W64 0 ∨
   uint.Z prev.(raft.entryID.index') ≤ uint.Z cv.(raft.Config.Applied')
     ≤ uint.Z (committed_after prev hs))%Z →
  (* the persisted ConfState: voters only *)
  voters ≠ [] → NoDup voters → W64 0 ∉ voters →
  cs.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 →
  cs.(raftpb.ConfState.Learners').(slice.len) = W64 0 →
  cs.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 →
  cs.(raftpb.ConfState.AutoLeave') = false →
  {{{ is_pkg_init raft ∗ c ↦ cv ∗ is_Logger lok ∗
      is_Storage (interface.ok si) ∗ own_Storage (interface.ok si) prev ents ∗
      □ (∀ Φ, own_Storage (interface.ok si) prev ents -∗
           (own_Storage (interface.ok si) prev ents -∗
            cs.(raftpb.ConfState.Voters') ↦*{dqv} voters -∗
            Φ (#hs, #cs, #interface.nil)%V) -∗
           WP #(methods si.(interface.ty) "InitialState"%go si.(interface.v)) #()
             {{ Φ }}) }}}
    @! raft.newRaft #c
  {{{ (r : loc) (s : nstate.t), RET #r;
      own_raft_phys (list_to_set voters) r cv.(raft.Config.ID') s ∗
      ⌜ nstate_wf s ∧
        s.(nstate.term) = hs.(raftpb.HardState.Term') ∧
        s.(nstate.vote) = hs.(raftpb.HardState.Vote') ∧
        s.(nstate.lead) = W64 0 ∧ s.(nstate.role) = role.Follower ∧
        s.(nstate.votes) = ∅ ∧ s.(nstate.outbox) = [] ⌝ }}}.

Module Type NEWRAFT.
  Parameter wp_newRaft : wp_newRaft_body.
  Arguments wp_newRaft {_ _ _ _ _ _ _ _}.
End NEWRAFT.
