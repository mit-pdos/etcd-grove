(** * Shared vocabulary for the election proof *)

Require Export New.proof.go_etcd_io.raft.v3_proof.base.
Require Export New.proof.go_etcd_io.raft.v3_proof.election_protocol.

(** Discharge a goal [¬ (W32 a = W32 b)] for distinct literals. *)
Ltac w32_ne :=
  intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.

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

End proof.
