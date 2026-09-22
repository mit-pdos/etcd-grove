Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceBecomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeReplicate.

Module BecomeLeaderPostulates : BECOMELEADER_POSTULATES.
  Include Reset.  Include TraceBecomeLeader.
  Include RaftLogLastIndex.
  Include RaftAppendEntry.
  Include ProgressBecomeReplicate.
End BecomeLeaderPostulates.

Module BecomeLeader := BecomeLeaderProof BecomeLeaderPostulates.
