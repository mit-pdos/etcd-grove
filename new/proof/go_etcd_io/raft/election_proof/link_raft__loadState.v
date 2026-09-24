Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__loadState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.

Module LoadStatePostulates : RAFT__LOADSTATE_POSTULATES.
  Include RaftLogLastIndex.
End LoadStatePostulates.

Module LoadState := LoadStateProof LoadStatePostulates.
