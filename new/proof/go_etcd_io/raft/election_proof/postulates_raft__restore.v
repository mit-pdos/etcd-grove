Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__commitTo.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MakeProgressTracker.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_confchange_Restore.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__switchToConfig.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_assertConfStatesEquivalent.

(** [restore]'s callees: the log's [matchTerm], [lastEntryID], [commitTo],
    [lastIndex] and [restore]; the tracker's rebuild ([MakeProgressTracker],
    [confchange.Restore], [switchToConfig], [assertConfStatesEquivalent]).
    The [Warningf]s and [becomeFollower] of the two dead exits are never
    reached. *)
Module Type RAFT__RESTORE_POSTULATES.
  Include RAFTLOG__MATCHTERM.
  Include RAFTLOG__LASTENTRYID.
  Include RAFTLOG__COMMITTO.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__RESTORE.
  Include MAKEPROGRESSTRACKER.
  Include CONFCHANGE_RESTORE.
  Include RAFT__SWITCHTOCONFIG.
  Include ASSERTCONFSTATESEQUIVALENT.
End RAFT__RESTORE_POSTULATES.
