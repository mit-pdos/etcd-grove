Require Export New.proof.go_etcd_io.raft.election_proof.spec_MajorityConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_slices_Sort.

(** Direct callee: [slices.Sort].  [l.AckedIndex] is called through the
    interface, so its triple is the caller-supplied [is_AckedIndexer]
    contract, not a postulate. *)
Module Type MAJORITYCONFIG__COMMITTEDINDEX_POSTULATES.
  Include SLICES_SORT.
End MAJORITYCONFIG__COMMITTEDINDEX_POSTULATES.
