Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_limitSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Entry__Size.

Module LimitSizePostulates : LIMITSIZE_POSTULATES.
  Include EntrySize.
End LimitSizePostulates.

Module LimitSize := LimitSizeProof LimitSizePostulates.
