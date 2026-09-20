Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__increaseUncommittedSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_payloadsSize.

Module RaftIncreaseUncommittedSizePostulates :
  RAFT__INCREASEUNCOMMITTEDSIZE_POSTULATES.
  Include PayloadsSize.
End RaftIncreaseUncommittedSizePostulates.

Module RaftIncreaseUncommittedSize :=
  RaftIncreaseUncommittedSizeProof RaftIncreaseUncommittedSizePostulates.
