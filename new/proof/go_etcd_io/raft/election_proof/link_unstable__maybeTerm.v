Require Export New.proof.go_etcd_io.raft.election_proof.proof_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__maybeLastIndex.

Module UnstableMaybeTermPostulates : UNSTABLE__MAYBETERM_POSTULATES.
  Include UnstableMaybeLastIndex.
End UnstableMaybeTermPostulates.

Module UnstableMaybeTerm := UnstableMaybeTermProof UnstableMaybeTermPostulates.
