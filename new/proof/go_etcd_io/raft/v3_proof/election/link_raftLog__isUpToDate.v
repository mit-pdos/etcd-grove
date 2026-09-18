Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raftLog__isUpToDate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastEntryID.

Module RaftLogIsUpToDatePostulates : RAFTLOG__ISUPTODATE_POSTULATES.
  Include RaftLogLastEntryID.
End RaftLogIsUpToDatePostulates.

Module RaftLogIsUpToDate := RaftLogIsUpToDateProof RaftLogIsUpToDatePostulates.
