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

## from 3h, round 1 (review F1: `Merge` writes in place)

`proto.Merge(dst, src)` merges into `dst`'s set submessages and appends to its repeated fields, in
place (`internal/impl/merge.go:159-184`, `merge_gen.go`): it needs every submessage and repeated
field `dst` reaches **owned, with its slices' capacity**. 3h's and W0's relation laws do not give
that for most messages (raftpb holds submessages and entries read-only for good and slices without
capacity; W0's `rangeRespOwn` holds `Kvs` without capacity), so `Merge.spec` at those types, as
stated today (`msgAt t p (own 1) c` only), is false of protobuf-go. Per type, what `Merge` needs:

- **raftpb (every type)**: never a destination (raft and etcd never merge raft messages). No 3h law
  gives the premise.
- **etcdserverpb `RangeResponse`** (the client's `GetStreamToGetResponse`): a destination built by
  `&pb.RangeResponse{}` and then only by `Merge` (3h's `rangeRespDst`, with `rangeRespDst_fresh`,
  `rangeRespDst_msgAt`, `rangeRespDst_own`).
- **every other etcd message**: never a destination.

Asked: restate `Merge.spec` with a per-type premise on the destination, given back after the merge;
3h declared it provisionally as `EtcdServerPb.mergeDstOk t p c` (`etcdserverpb/Api.lean`, opaque):
`{msgAt t p (own 1) c ∗ mergeDstOk t p c ∗ msgAt t q dq c'} Merge(p, q) {msgAt t p (own 1) (merge c
c') ∗ mergeDstOk t p (merge c c') ∗ msgAt t q dq c'}` (move the name into `Proto` if you prefer; 3h
renames). And in the header, one line per generic spec on what it does to the holder (Clone reads;
Size and Marshal write only `sizeCache`; Unmarshal resets, then writes fresh cells; Merge writes in
place), checked against each owner's laws.

Also (review, second tier 4): **a content records its message type** (an empty `AuthEnableRequest`
and an empty `AuthDisableRequest` must be different contents, or 3h's `holds_fun` is inconsistent):
`proto.Equal` compares descriptors first, so "up to `proto.Equal`" implies it; please say so in
`Proto/Api.lean` (or a law `msgAt t p dq c ∗ msgAt t' p' dq' c ⊢ ⌜t = t'⌝`).

To W0 (noted here, W0 reads it via the coordinator): `GetStreamToGetResponse.spec`'s accumulator is
3h's `rangeRespDst` (fresh, merged into, then `rangeRespDst_own` to return a `rangeRespOwn`).
