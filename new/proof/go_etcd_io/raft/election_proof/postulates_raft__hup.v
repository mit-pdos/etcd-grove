Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__hup.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__campaign.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__promotable.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__hasUnappliedConfChanges.
(* [step_campaign_state]; last, so that [step] is the protocol's *)
Require Export New.proof.go_etcd_io.raft.election_proof.step_lemmas.

Module Type HUP_POSTULATES.
  Include CAMPAIGN.  Include RAFT__PROMOTABLE.
  Include RAFT__HASUNAPPLIEDCONFCHANGES.
End HUP_POSTULATES.
