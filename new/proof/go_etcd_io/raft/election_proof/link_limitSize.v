Require Export New.proof.go_etcd_io.raft.election_proof.proof_limitSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Entry__Size.

Module LimitSizePostulates : LIMITSIZE_POSTULATES.
  Include EntrySize.
End LimitSizePostulates.

Module LimitSize := LimitSizeProof LimitSizePostulates.
