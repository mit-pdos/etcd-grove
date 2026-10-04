Require Export New.proof.go_etcd_io.raft.election_proof.proof_readOnly__maybeAdvance.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_readOnly__AckedIndex.

Module ReadOnlyMaybeAdvancePostulates : READONLY__MAYBEADVANCE_POSTULATES.
  Include JointConfigCommittedIndex.
  Include ReadOnlyAckedIndex.
End ReadOnlyMaybeAdvancePostulates.

Module ReadOnlyMaybeAdvance :=
  ReadOnlyMaybeAdvanceProof ReadOnlyMaybeAdvancePostulates.
