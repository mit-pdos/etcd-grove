Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__switchToConfig.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceConfChangeEvent.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__ConfState.

Module Type RAFT__SWITCHTOCONFIG_POSTULATES.
  Include TRACECONFCHANGEEVENT.  Include PROGRESSTRACKER__CONFSTATE.
End RAFT__SWITCHTOCONFIG_POSTULATES.
