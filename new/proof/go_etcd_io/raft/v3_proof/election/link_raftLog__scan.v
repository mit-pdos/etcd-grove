Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__scan.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__slice.

Module RaftLogScanPostulates : RAFTLOG__SCAN_POSTULATES.
  Include RaftLogSlice.
End RaftLogScanPostulates.

Module RaftLogScan := RaftLogScanProof RaftLogScanPostulates.
