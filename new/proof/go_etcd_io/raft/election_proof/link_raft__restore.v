Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__commitTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MakeProgressTracker.
Require Export New.proof.go_etcd_io.raft.election_proof.link_confchange_Restore.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__switchToConfig.
Require Export New.proof.go_etcd_io.raft.election_proof.link_assertConfStatesEquivalent.

Module RaftRestorePostulates : RAFT__RESTORE_POSTULATES.
  Include RaftLogMatchTerm.
  Include RaftLogLastEntryID.
  Include RaftLogCommitTo.
  Include RaftLogLastIndex.
  Include RaftLogRestore.
  Include MakeProgressTracker.
  Include ConfchangeRestore.
  Include SwitchToConfig.
  Include AssertConfStatesEquivalent.
End RaftRestorePostulates.

Module RaftRestore := RaftRestoreProof RaftRestorePostulates.
