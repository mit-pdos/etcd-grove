Require Export New.proof.go_etcd_io.raft.election_proof.spec_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MajorityConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_matchAckIndexer__AckedIndex.

(** Direct callee: [MajorityConfig.CommittedIndex].  [matchAckIndexer.
    AckedIndex] is called from inside it through the interface; its triple
    is what this proof uses to build the [is_AckedIndexer] contract. *)
Module Type JOINTCONFIG__COMMITTEDINDEX_POSTULATES.
  Include MAJORITYCONFIG__COMMITTEDINDEX.
  Include MATCHACKINDEXER__ACKEDINDEX.
End JOINTCONFIG__COMMITTEDINDEX_POSTULATES.
