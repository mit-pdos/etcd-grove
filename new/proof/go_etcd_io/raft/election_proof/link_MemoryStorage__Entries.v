Require Export New.proof.go_etcd_io.raft.election_proof.proof_MemoryStorage__Entries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MemoryStorage__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_limitSize.

Module MemoryStoragePublicEntriesPostulates : MEMORYSTORAGE__PUBLIC_ENTRIES_POSTULATES.
  Include MemoryStorageLastIndex.
  Include LimitSize.
End MemoryStoragePublicEntriesPostulates.

Module MemoryStoragePublicEntries := MemoryStoragePublicEntriesProof MemoryStoragePublicEntriesPostulates.
