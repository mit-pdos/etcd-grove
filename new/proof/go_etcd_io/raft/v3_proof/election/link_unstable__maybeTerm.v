Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeLastIndex.

Module UnstableMaybeTermPostulates : UNSTABLE__MAYBETERM_POSTULATES.
  Include UnstableMaybeLastIndex.
End UnstableMaybeTermPostulates.

Module UnstableMaybeTerm := UnstableMaybeTermProof UnstableMaybeTermPostulates.
