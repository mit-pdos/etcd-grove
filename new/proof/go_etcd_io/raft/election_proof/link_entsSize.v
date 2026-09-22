Require Export New.proof.go_etcd_io.raft.election_proof.proof_entsSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Entry__Size.

Module EntsSizePostulates : ENTSSIZE_POSTULATES.
  Include EntrySize.
End EntsSizePostulates.

Module EntsSize := EntsSizeProof EntsSizePostulates.
