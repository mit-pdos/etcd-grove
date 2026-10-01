Require Export New.proof.go_etcd_io.raft.election_proof.spec_unstable__truncateAndAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__slice.

Module Type UNSTABLE__TRUNCATEANDAPPEND_POSTULATES.
  (* arm 3 calls [u.slice(u.offset, fromIndex)] *)
  Include UNSTABLE__SLICE.
End UNSTABLE__TRUNCATEANDAPPEND_POSTULATES.
