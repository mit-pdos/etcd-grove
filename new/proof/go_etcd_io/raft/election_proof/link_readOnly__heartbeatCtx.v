Require Export New.proof.go_etcd_io.raft.election_proof.proof_readOnly__heartbeatCtx.

Module ReadOnlyHeartbeatCtxPostulates : READONLY__HEARTBEATCTX_POSTULATES.
End ReadOnlyHeartbeatCtxPostulates.

Module ReadOnlyHeartbeatCtx :=
  ReadOnlyHeartbeatCtxProof ReadOnlyHeartbeatCtxPostulates.
