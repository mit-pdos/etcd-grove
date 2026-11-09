# Requirements on `go.etcd.io/etcd/api/v3/etcdserverpb` and `mvccpb` (the messages, batch 3h)

## from W0

W0 defined the KV messages' heap predicates the client and the server share
(`Spec/go_etcd_io/etcd/api/v3/Wire.lean`, namespace `EtcdWire`): `rangeReqOwn`, `putReqOwn`,
`deleteReqOwn`, `compareOwn`, `requestOpOwn`, `txnReqOwn`, `compactReqOwn` (requests, over
`Model.lean`'s `RangeReq`, ...) and `respHeaderOwn`, `keyValueOwn`, `rangeRespOwn`, `putRespOwn`,
`deleteRespOwn`, `responseOpOwn`, `txnRespOwn`, `compactRespOwn` (replies, over Go-level models),
with `protoRest` for the protobuf bookkeeping, each with an unfold law (field by field). They are
opaque: 3h realizes them from its own message vocabulary and proves the laws.

1. **Realize the predicates and prove their laws**: `*_unfold`, `protoRest_zero`, `replyPersist`,
   `msgOwn_ne_null`. If 3h's vocabulary makes a different shape necessary (the oneof wrappers,
   `protoRest`'s fields), say so in a `req/` to W0 rather than working around it.

2. **The generated getters** over these predicates (pointer receivers, nil-safe as protobuf's):
   `ResponseOp.GetResponseRange`, `GetResponsePut`, `GetResponseDeleteRange`, `GetResponseTxn`
   (the wrapped reply's pointer for the matching `responseOneof` case, `nil` otherwise),
   `RequestOp.GetRequestRange` (used by the server's `IsTxnReadonly`), `Compare.GetKey` (nil-safe:
   `nil` for a nil message), `RangeResponse.GetKvs`, `GetHeader`, `ResponseHeader.GetRevision`.
   ```go
   rr := resp.Responses[0].GetResponseRange()      // nil unless the else-branch ran a get
   if rr != nil && len(rr.Kvs) == 1 { ... }
   ```
   Used by: the snippets `clientv3kv/txn.go`; `Cmp.KeyBytes.spec` (`Compare.GetKey`).

3. **The enum name maps** (`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`): their
   init law (the maps hold exactly `0..2`, `0..4`).
   Used by: `Op.IsSortOptionValid.spec`.

4. **`NewKVClient(conn)`** (the generated stub): for `connOk conn γ who` (1c) it returns a value with
   `remoteKVAt v γ who` (`client/v3/Api.lean`), its methods `cc.Invoke`/`cc.NewStream` with the
   method names, a fresh reply message (`new(RangeResponse)`, ...) unmarshalled by grpc
   (`req/google_golang_org_grpc.md`), and the stream's `Recv` (`wireStreamAt_recv`).
   Used by: `RetryKVClient.spec`.

5. **`proto.Clone` of a `*pb.Compare`** (protobuf's boundary, 2a's proto): a fresh deep copy,
   owned (`compareOwn p' (own 1) m` from `compareOwn p dq m`). **`proto.Merge`** of
   `RangeResponse`s (repeated `Kvs` appended, `Header`/`More`/`Count` taken when set).
   Used by: `cloneCompare.spec`, `GetStreamToGetResponse.spec`.
