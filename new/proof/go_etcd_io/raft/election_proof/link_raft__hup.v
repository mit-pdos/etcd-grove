Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__hup.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__campaign.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__promotable.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__hasUnappliedConfChanges.

Module HupPostulates : HUP_POSTULATES.
  Include Campaign.  Include RaftPromotable.
  Include RaftHasUnappliedConfChanges.
End HupPostulates.

Module Hup := HupProof HupPostulates.
