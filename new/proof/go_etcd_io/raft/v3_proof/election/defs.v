(** * Shared vocabulary for the election proof *)

Require Export New.proof.go_etcd_io.raft.v3_proof.base.
Require Export New.proof.go_etcd_io.raft.v3_proof.election_protocol.

(** Discharge a goal [¬ (W32 a = W32 b)] for distinct literals. *)
Ltac w32_ne :=
  intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.

(** Introduce the binders every [wp_<fn>_body] opens with.  The one place this
    list is written; see notes/gotchas.md. *)
Ltac intros_ambient :=
  intros ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** ** Message-type constants, as Rocq values

    [raftpb.MessageType] is a [w32]; the Goose constants are opaque [val]s,
    so we name the underlying numbers. *)
Definition MsgHup : w32 := W32 0.
Definition MsgApp : w32 := W32 3.
Definition MsgAppResp : w32 := W32 4.
Definition MsgVote : w32 := W32 5.
Definition MsgVoteResp : w32 := W32 6.
Definition MsgSnap : w32 := W32 7.
Definition MsgHeartbeat : w32 := W32 8.
Definition MsgPreVote : w32 := W32 17.
Definition MsgPreVoteResp : w32 := W32 18.
Definition MsgStorageAppendResp : w32 := W32 20.

Definition StateFollower : w64 := W64 0.
Definition StateCandidate : w64 := W64 1.
Definition StateLeader : w64 := W64 2.

Definition campaignElection : raft.CampaignType.t := "CampaignElection"%go.
Definition campaignPreElection : raft.CampaignType.t := "CampaignPreElection"%go.
Definition campaignTransfer : raft.CampaignType.t := "CampaignTransfer"%go.

Definition VotePending : w8 := W8 1.
Definition VoteLost : w8 := W8 2.
Definition VoteWon : w8 := W8 3.

Definition state_w64 (ro : role.t) : w64 :=
  match ro with
  | role.Follower => StateFollower
  | role.Candidate => StateCandidate
  | role.Leader => StateLeader
  end.

(** ** Abstraction of physical messages

    Only election-related message types have an abstraction. *)
Definition mtype_of (t : w32) : option mtype.t :=
  if decide (t = MsgVote) then Some mtype.Vote
  else if decide (t = MsgVoteResp) then Some mtype.VoteResp
  else if decide (t = MsgApp) then Some mtype.App
  else if decide (t = MsgHeartbeat) then Some mtype.Heartbeat
  else None.

Lemma mtype_of_MsgVote : mtype_of MsgVote = Some mtype.Vote.
Proof. rewrite /mtype_of. case_decide as H1; [done|congruence]. Qed.

Lemma mtype_of_MsgVoteResp : mtype_of MsgVoteResp = Some mtype.VoteResp.
Proof.
  rewrite /mtype_of. case_decide as H1.
  { exfalso. rewrite /MsgVoteResp /MsgVote in H1. word. }
  case_decide as H2; [done|congruence].
Qed.

Definition abs_msg (ty : mtype.t) (m : raftpb.Message.t) : msg.t :=
  msg.mk ty m.(raftpb.Message.From') m.(raftpb.Message.To')
            m.(raftpb.Message.Term') m.(raftpb.Message.Reject').

(** The partial abstraction of a physical message: [None] for the message
    types the election model does not describe.  [MsgAppResp] is the one that
    matters — [appendEntry] queues one, so a total abstraction would make the
    abstract outbox undefined exactly where [becomeLeader] needs it. *)
Definition abs_msg_opt (m : raftpb.Message.t) : option msg.t :=
  ty ← mtype_of m.(raftpb.Message.Type'); Some (abs_msg ty m).

Lemma abs_msg_opt_Some ty m :
  mtype_of m.(raftpb.Message.Type') = Some ty → abs_msg_opt m = Some (abs_msg ty m).
Proof. rewrite /abs_msg_opt => ->. done. Qed.

(** The abstract outbox of the two physical queues, together. *)
Definition abs_outbox (msgs msgsAA : list raftpb.Message.t) : list msg.t :=
  omap abs_msg_opt msgs ++ omap abs_msg_opt msgsAA.

(** [send] appends to one queue or the other depending on the message type.
    The abstract outbox grows at the end either way — but only up to
    permutation, which is why [own_raft_phys] relates the two with [≡ₚ]. *)
Lemma abs_outbox_snoc_msgs (msgs msgsAA : list raftpb.Message.t) m ty :
  mtype_of m.(raftpb.Message.Type') = Some ty →
  abs_outbox (msgs ++ [m]) msgsAA ≡ₚ abs_outbox msgs msgsAA ++ [abs_msg ty m].
Proof.
  intros Hty. rewrite /abs_outbox omap_app /=.
  rewrite (abs_msg_opt_Some ty) //= -!assoc.
  apply Permutation_app_head, Permutation_app_comm.
Qed.

Lemma abs_outbox_snoc_msgsAA (msgs msgsAA : list raftpb.Message.t) m ty :
  mtype_of m.(raftpb.Message.Type') = Some ty →
  abs_outbox msgs (msgsAA ++ [m]) ≡ₚ abs_outbox msgs msgsAA ++ [abs_msg ty m].
Proof.
  intros Hty. rewrite /abs_outbox omap_app /=.
  rewrite (abs_msg_opt_Some ty) //= assoc //.
Qed.

(** A message the model does not describe leaves the abstract outbox alone. *)
Lemma abs_outbox_snoc_msgsAA_None (msgs msgsAA : list raftpb.Message.t) m :
  mtype_of m.(raftpb.Message.Type') = None →
  abs_outbox msgs (msgsAA ++ [m]) = abs_outbox msgs msgsAA.
Proof.
  intros Hty. rewrite /abs_outbox omap_app /= /abs_msg_opt Hty /=.
  by rewrite app_nil_r.
Qed.

End proof.
