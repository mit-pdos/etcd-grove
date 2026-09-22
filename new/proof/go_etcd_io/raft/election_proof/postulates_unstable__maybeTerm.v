Require Export New.proof.go_etcd_io.raft.election_proof.spec_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeLastIndex.

Module Type UNSTABLE__MAYBETERM_POSTULATES.
  (* the [i >= offset] branch calls [maybeLastIndex] *)
  Include UNSTABLE__MAYBELASTINDEX.
End UNSTABLE__MAYBETERM_POSTULATES.
