Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_payloadsSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_payloadSize.

Module PayloadsSizePostulates : PAYLOADSSIZE_POSTULATES.
  Include PayloadSize.
End PayloadsSizePostulates.

Module PayloadsSize := PayloadsSizeProof PayloadsSizePostulates.
