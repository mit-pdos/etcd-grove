(** Pure lemmas shared by [Step]'s pre-vote branches
    ([proof_raft__Step_MsgPreVote*.v], [proof_raft__Step_MsgPreVoteResp*.v]),
    2026-10-04.

    Proof structure, not specification: no [Module Type], no [Parameter],
    no Hoare triple.  Each lemma takes a [stepX] result relation apart for
    [MsgPreVoteResp], outside any WP, where the [decide] chains are cheap.
    Only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Section prevote.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

(** [stepFollower] has no [MsgPreVoteResp] arm. *)
Lemma follower_step_result_prevoteresp id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgPreVoteResp →
  follower_step_result id s m ents sv dropped s' → dropped = false ∧ s' = s.
Proof.
  intros Hty. rewrite /follower_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [exfalso; revert H3; w32_ne|].
  case_decide as H4; [exfalso; revert H4; w32_ne|].
  case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
  case_decide as H6; [exfalso; revert H6; w32_ne|].
  case_decide as H7; done.
Qed.

(** [stepLeader] has none either. *)
Lemma leader_step_result_prevoteresp id s m ents dropped s' :
  m.(raftpb.Message.Type') = MsgPreVoteResp →
  leader_step_result cfg id s m ents dropped s' → dropped = false ∧ s' = s.
Proof.
  intros Hty. rewrite /leader_step_result.
  case_decide as H1; [exfalso; rewrite Hty in H1; revert H1; w32_ne|].
  intros [-> Hres]. split; first done.
  destruct Hres as [[_ ->]|[[Hc _]|[[Hc _]|[Hc _]]]]; first done;
    exfalso; rewrite Hty in Hc; revert Hc; w32_ne.
Qed.

(** [stepCandidate] on a [MsgPreVoteResp]: nothing at a candidate; at a
    pre-candidate, the tally and then win / lose / wait, which is
    [step_prevote_resp_result]. *)
Lemma candidate_step_result_prevoteresp id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgPreVoteResp →
  (s.(nstate.role) = prole.Candidate ∨ s.(nstate.role) = prole.PreCandidate) →
  id ∈ cfg →
  uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
  nstate_wf s →
  candidate_step_result cfg id s m ents sv dropped s' →
  dropped = false ∧ nstate_wf s' ∧ step cfg id (to_pstate s) [] (to_pstate s').
Proof.
  intros Hty Hrole Hin Hnw Hwf. rewrite /candidate_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [exfalso; revert H3; w32_ne|].
  case_decide as H4; [exfalso; revert H4; w32_ne|].
  case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
  case_decide as H6; [exfalso; revert H6; w32_ne|].
  case_decide as H7; [|by intros []].
  intros [-> Hres]. split; first done.
  revert Hres. destruct (decide (s.(nstate.role) = prole.PreCandidate)) as [Hp|Hp].
  - intros (won & lost & peers & pvs & Hw & Hl & ->).
    split; first by apply nstate_wf_prvals, nstate_wf_prevote_resp_result.
    apply step_prevote_resp_result; [exact Hp|exact Hin|exact Hnw|].
    intros Hwon. by destruct (Hw Hwon).
  - intros ->. split; [exact Hwf|apply step_refl].
Qed.

End prevote.
