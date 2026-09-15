Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__campaign.

Module HupPostulates : HUP_POSTULATES.
  Include Campaign.
End HupPostulates.

Module Hup := HupProof HupPostulates.
