Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_entsSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Entry__Size.

Module EntsSizePostulates : ENTSSIZE_POSTULATES.
  Include EntrySize.
End EntsSizePostulates.

Module EntsSize := EntsSizeProof EntsSizePostulates.
