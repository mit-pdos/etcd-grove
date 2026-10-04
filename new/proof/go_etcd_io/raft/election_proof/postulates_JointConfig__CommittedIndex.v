Require Export New.proof.go_etcd_io.raft.election_proof.spec_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MajorityConfig__CommittedIndex.

(** Direct callee: [MajorityConfig.CommittedIndex]; the indexer's
    [AckedIndex] is reached from inside it through [is_AckedIndexer]. *)
Module Type JOINTCONFIG__COMMITTEDINDEX_POSTULATES.
  Include MAJORITYCONFIG__COMMITTEDINDEX.
End JOINTCONFIG__COMMITTEDINDEX_POSTULATES.
