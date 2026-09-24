Require Export New.proof.go_etcd_io.raft.election_proof.proof_newRaft.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Config__validate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_newLogWithSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MakeProgressTracker.
Require Export New.proof.go_etcd_io.raft.election_proof.link_newReadOnly.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceInitState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_confchange_Restore.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__switchToConfig.
Require Export New.proof.go_etcd_io.raft.election_proof.link_assertConfStatesEquivalent.
Require Export New.proof.go_etcd_io.raft.election_proof.link_IsEmptyHardState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__loadState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__appliedTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__VoterNodes.
Require Export New.proof.go_etcd_io.raft.election_proof.link_fmt_Sprintf.
Require Export New.proof.go_etcd_io.raft.election_proof.link_strings_Join.

Module NewRaftPostulates : NEWRAFT_POSTULATES.
  Include ConfigValidate.  Include NewLogWithSize.  Include MakeProgressTracker.  Include NewReadOnly.  Include TraceInitState.  Include RaftLogLastEntryID.  Include ConfchangeRestore.  Include SwitchToConfig.  Include AssertConfStatesEquivalent.  Include IsEmptyHardState.  Include LoadState.  Include RaftLogAppliedTo.  Include BecomeFollower.  Include ProgressTrackerVoterNodes.  Include FmtSprintf.  Include StringsJoin.
End NewRaftPostulates.

Module NewRaft := NewRaftProof NewRaftPostulates.
