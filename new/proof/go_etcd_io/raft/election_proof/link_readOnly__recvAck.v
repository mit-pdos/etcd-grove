Require Export New.proof.go_etcd_io.raft.election_proof.proof_readOnly__recvAck.

Module ReadOnlyRecvAckPostulates : READONLY__RECVACK_POSTULATES.
End ReadOnlyRecvAckPostulates.

Module ReadOnlyRecvAck :=
  ReadOnlyRecvAckProof ReadOnlyRecvAckPostulates.
