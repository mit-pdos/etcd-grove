Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__appendEntry.

Module RaftAppendEntryPostulates : RAFT__APPENDENTRY_POSTULATES.
End RaftAppendEntryPostulates.

Module RaftAppendEntry := RaftAppendEntryProof RaftAppendEntryPostulates.
