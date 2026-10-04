Require Export New.proof.go_etcd_io.raft.election_proof.spec_MemoryStorage__Entries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MemoryStorage__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_limitSize.

Module Type MEMORYSTORAGE__PUBLIC_ENTRIES_POSTULATES.
  Include MEMORYSTORAGE__LASTINDEX.
  Include LIMITSIZE.
End MEMORYSTORAGE__PUBLIC_ENTRIES_POSTULATES.
