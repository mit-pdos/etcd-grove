Require Export New.proof.go_etcd_io.raft.election_proof.proof_readOnly__AckedIndex.

Module ReadOnlyAckedIndexPostulates : READONLY__ACKEDINDEX_POSTULATES.
End ReadOnlyAckedIndexPostulates.

Module ReadOnlyAckedIndex :=
  ReadOnlyAckedIndexProof ReadOnlyAckedIndexPostulates.
