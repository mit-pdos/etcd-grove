Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__snapshot.

Module RaftLogSnapshotPostulates : RAFTLOG__SNAPSHOT_POSTULATES.
End RaftLogSnapshotPostulates.

Module RaftLogSnapshot := RaftLogSnapshotProof RaftLogSnapshotPostulates.
