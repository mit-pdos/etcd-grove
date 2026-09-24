Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__switchToConfig.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceConfChangeEvent.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__ConfState.

Module SwitchToConfigPostulates : RAFT__SWITCHTOCONFIG_POSTULATES.
  Include TraceConfChangeEvent.  Include ProgressTrackerConfState.
End SwitchToConfigPostulates.

Module SwitchToConfig := SwitchToConfigProof SwitchToConfigPostulates.
