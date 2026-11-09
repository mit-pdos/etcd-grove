# Requirements on `google.golang.org/protobuf/proto` (batch 2a: the proto boundary)

## from R3

- `proto.Size(m)` of a raft `*Entry` (held read-only, R3's provisional `entryRO p k e` / R1's
  `entriesRO`): returns some `int` (no panic, nothing written). raft only sums it into budgets, so no
  value is needed.
  ```go
  size += entryEncodingSize(proto.Size(ent)) // util.go: entsSize, limitSize
  ```
  Used by: `entsSize.spec`, `limitSize.spec` (and through them `raftLog.slice.spec`,
  `MemoryStorage.Entries.spec`).
- `proto.Clone` of a `*Snapshot`: see `go_etcd_io_raft_v3_raftpb.md` (R1, R3).
