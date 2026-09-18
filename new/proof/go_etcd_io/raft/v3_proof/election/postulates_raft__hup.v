Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__promotable.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__hasUnappliedConfChanges.

Module Type HUP_POSTULATES.
  Include CAMPAIGN.  Include RAFT__PROMOTABLE.
  Include RAFT__HASUNAPPLIEDCONFCHANGES.
End HUP_POSTULATES.
