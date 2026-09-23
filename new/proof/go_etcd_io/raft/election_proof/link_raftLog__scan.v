Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__scan.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__slice.

Module RaftLogScanPostulates : RAFTLOG__SCAN_POSTULATES.
  Include RaftLogSlice.
End RaftLogScanPostulates.

Module RaftLogScan := RaftLogScanProof RaftLogScanPostulates.
