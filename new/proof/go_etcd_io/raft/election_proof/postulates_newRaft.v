Require Export New.proof.go_etcd_io.raft.election_proof.spec_newRaft.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Config__validate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newLogWithSize.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MakeProgressTracker.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newReadOnly.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceInitState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_confchange_Restore.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__switchToConfig.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_assertConfStatesEquivalent.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_IsEmptyHardState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__loadState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__appliedTo.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__VoterNodes.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_fmt_Sprintf.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_strings_Join.

Module Type NEWRAFT_POSTULATES.
  Include CONFIG__VALIDATE.  Include NEWLOGWITHSIZE.  Include MAKEPROGRESSTRACKER.  Include NEWREADONLY.  Include TRACEINITSTATE.  Include RAFTLOG__LASTENTRYID.  Include CONFCHANGE_RESTORE.  Include RAFT__SWITCHTOCONFIG.  Include ASSERTCONFSTATESEQUIVALENT.  Include ISEMPTYHARDSTATE.  Include RAFT__LOADSTATE.  Include RAFTLOG__APPLIEDTO.  Include BECOMEFOLLOWER.  Include PROGRESSTRACKER__VOTERNODES.  Include FMT_SPRINTF.  Include STRINGS_JOIN.
End NEWRAFT_POSTULATES.
