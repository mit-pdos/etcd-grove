Require Export New.proof.go_etcd_io.raft.election_proof.proof_payloadsSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_payloadSize.

Module PayloadsSizePostulates : PAYLOADSSIZE_POSTULATES.
  Include PayloadSize.
End PayloadsSizePostulates.

Module PayloadsSize := PayloadsSizeProof PayloadsSizePostulates.
