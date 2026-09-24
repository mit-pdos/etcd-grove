Require Export New.proof.go_etcd_io.raft.election_proof.proof_fmt_Sprintf.

Module FmtSprintfPostulates : FMT_SPRINTF_POSTULATES.
End FmtSprintfPostulates.

Module FmtSprintf := FmtSprintfProof FmtSprintfPostulates.
