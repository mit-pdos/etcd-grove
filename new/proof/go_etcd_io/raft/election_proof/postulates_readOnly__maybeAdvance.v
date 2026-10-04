Require Export New.proof.go_etcd_io.raft.election_proof.spec_readOnly__maybeAdvance.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__AckedIndex.

(** Direct callee: [JointConfig.CommittedIndex] (the general-indexer
    triple), whose indexer is this object, through the interface:
    [readOnly.AckedIndex]'s triple is what builds the [is_AckedIndexer]
    contract. *)
Module Type READONLY__MAYBEADVANCE_POSTULATES.
  Include JOINTCONFIG__COMMITTEDINDEX.
  Include READONLY__ACKEDINDEX.
End READONLY__MAYBEADVANCE_POSTULATES.
