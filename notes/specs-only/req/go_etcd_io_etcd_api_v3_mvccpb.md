# Requirements on `go.etcd.io/etcd/api/v3/mvccpb` (3h)

## from 3e

mvcc marshals a `mvccpb.KeyValue` for each change it writes to the storage (`storeTxnWrite.put`,
`delete`: `proto.Marshal(kv)`, `lg.Fatal` on an error) and unmarshals each one it reads back
(`rangeKeys`, `restoreChunk`: `proto.Unmarshal(vs[0], kv)`, `lg.Fatal` on an error). Its results are
stated with W0's `EtcdWire.keyValueOwn p dq m` (`KeyValueM`). What it needs, through the proto
boundary (`Spec/google_golang_org/protobuf/proto/`):

1. **The content relation**: `keyValueOwn p dq m ⊣⊢ Proto.msgAt mvccpb.KeyValue.ty p dq (kvContent m)`
   for a pure `kvContent : KeyValueM → Proto.Content` (3h's `*_msgAt` laws, as for the other
   messages), injective.
2. **A key-value always marshals**: `Proto.marshalOk (kvContent m)` (its fields are bytes and
   integers: no string to validate) and `depth (kvContent m) = 1`; and its size: `(kvContent
   m).fits` when `m.key.length + m.value.length` is below a named bound (the proto boundary's
   `marshalMax = 2 ^ 48`, less the fixed fields' encoding). **Open** (3e's report): where a store's
   key and value sizes are bounded (a workload premise on the store's producer, as
   `examples/reply-size.md`; or gRPC's request size, 2a's `v3rpcBootCfg`).
3. **Decoding what was encoded**: `encodes KeyValue.ty c bs → encodes KeyValue.ty c' bs → c = c'`
   (the boundary's `encodes_fun`) suffices with 1.
```go
d, err := proto.Marshal(kv)          // kvstore_txn.go:247 (put), :315 (delete)
if err := proto.Unmarshal(vs[0], kv) // kvstore_txn.go:136 (rangeKeys), kvstore.go:498 (restoreChunk)
```
Used by: `storeTxnWrite.put.spec`, `storeTxnWrite.delete.spec`, `storeTxnCommon.rangeKeys.spec`,
`restoreChunk.spec`, and through them `Txn.Range`'s full read (`KeyValueM.ofKV` of each record).
