Require Export New.proof.go_etcd_io.raft.election_proof.proof_Config__validate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_IsLocalMsgTarget.

Module ConfigValidatePostulates : CONFIG__VALIDATE_POSTULATES.
  Include IsLocalMsgTarget.
End ConfigValidatePostulates.

Module ConfigValidate := ConfigValidateProof ConfigValidatePostulates.
