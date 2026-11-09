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

## from 3h

Batch 3h (`Spec/go_etcd_io/raft/v3/raftpb/`, `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/`) relates
every message predicate to `Proto.msgAt` through content relations (`entryIs`, `msgIs`, ...,
`reqHolds`, `rangeRespHolds`, ...: `*_msgAt` laws). Three facts of protobuf-go it needs that are
not in the boundary yet:

1. **`Marshal` is deterministic for a message type without map fields**: its bytes are a function
   of the content, `Proto.marshalOut t c` (with `encodes t c (marshalOut t c)`), and `Marshal.spec`'s
   success case returns exactly `marshalOut t c` for such a `t`. True of protobuf-go (fields encoded
   in field-number order, `orderedCoderFields`; only map iteration is randomized, and unknown fields
   are appended as stored). raft's founders must append the same bootstrap entry bytes.
   ```go
   data, err := proto.Marshal(cc) // raft bootstrap.go:56, at every founder
   ```
   Used by: R1's `RawNode.Bootstrap.spec`/`StartNode.spec` (`BootLog`), through 3h's
   `bootEntryData` (opaque until then; `bootCC_facts` gives only `encodes`). Snippet:
   `examples/specreq/raftpb/snapshot.go` (`ReqBootstrapBytes`).
2. **The empty bytes decode to the zero message of any type**: a content `Proto.zero` (or one per
   type) with `encodes t zero []` and `depth zero = 1`, which a fresh `new(T)` holds (the zero
   struct's `msgAt`). 3h's readers then state the zero model (`decodeConfChange_empty`: the
   auto-leave entry `MarshalConfChange(nil)` appends with no data decodes to the empty
   `ConfChangeV2`).
   ```go
   if err := proto.Unmarshal(e.GetData(), &ccc); err != nil { panic(err) } // raft.go:1338, nil data
   ```
   Used by: `decodeConfChange_empty.spec` (R2's `stepIn`, the auto-leave entry).
3. **A shared bookkeeping predicate**: W0's `EtcdWire.protoRest t p dq` and 3h's `RaftPb.pbRest t p
   dq` are the same thing (the `state`, `sizeCache`, `unknownFields` fields of a generated message);
   one definition in `Proto` would serve both (optional; integration can identify them).
