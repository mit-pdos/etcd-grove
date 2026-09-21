Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raftLog__snapshot.

(** No raft callees: the one call in the body is [Storage.Snapshot], whose
    triple is part of [is_Storage] ([inv_storage.v]). *)
Module Type RAFTLOG__SNAPSHOT_POSTULATES.
End RAFTLOG__SNAPSHOT_POSTULATES.
