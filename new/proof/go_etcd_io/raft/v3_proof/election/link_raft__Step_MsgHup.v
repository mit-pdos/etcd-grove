(** * Link: [raft.raft__Step_MsgHup]

    [raft__Step_MsgHup] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_MsgHup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__hup.

Module StepMsgHupPostulates : STEP_MSGHUP_POSTULATES.
  Include Hup.
End StepMsgHupPostulates.

Module StepMsgHup := StepMsgHupProof StepMsgHupPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments StepMsgHup.wp_raft__Step_MsgHup {_ _ _ _ _ _ _ _}.
