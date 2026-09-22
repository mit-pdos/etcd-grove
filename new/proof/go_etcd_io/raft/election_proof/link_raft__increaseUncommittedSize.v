Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__increaseUncommittedSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_payloadsSize.

Module RaftIncreaseUncommittedSizePostulates :
  RAFT__INCREASEUNCOMMITTEDSIZE_POSTULATES.
  Include PayloadsSize.
End RaftIncreaseUncommittedSizePostulates.

Module RaftIncreaseUncommittedSize :=
  RaftIncreaseUncommittedSizeProof RaftIncreaseUncommittedSizePostulates.
