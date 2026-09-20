Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__scan.

Module RaftLogScanProof (P : RAFTLOG__SCAN_POSTULATES) : RAFTLOG__SCAN.
Import P.

  Lemma wp_raftLog__scan_at : wp_raftLog__scan_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents lo hi pageSize f I P Hrange HP.
  Admitted.

End RaftLogScanProof.
