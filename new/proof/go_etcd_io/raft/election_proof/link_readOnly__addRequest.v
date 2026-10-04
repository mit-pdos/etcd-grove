Require Export New.proof.go_etcd_io.raft.election_proof.proof_readOnly__addRequest.

Module ReadOnlyAddRequestPostulates : READONLY__ADDREQUEST_POSTULATES.
End ReadOnlyAddRequestPostulates.

Module ReadOnlyAddRequest :=
  ReadOnlyAddRequestProof ReadOnlyAddRequestPostulates.
