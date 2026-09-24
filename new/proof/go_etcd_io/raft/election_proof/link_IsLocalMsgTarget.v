Require Export New.proof.go_etcd_io.raft.election_proof.proof_IsLocalMsgTarget.

Module IsLocalMsgTargetPostulates : ISLOCALMSGTARGET_POSTULATES.
End IsLocalMsgTargetPostulates.

Module IsLocalMsgTarget := IsLocalMsgTargetProof IsLocalMsgTargetPostulates.
