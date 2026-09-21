Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__snapshot.

Module RaftLogSnapshotPostulates : RAFTLOG__SNAPSHOT_POSTULATES.
End RaftLogSnapshotPostulates.

Module RaftLogSnapshot := RaftLogSnapshotProof RaftLogSnapshotPostulates.
