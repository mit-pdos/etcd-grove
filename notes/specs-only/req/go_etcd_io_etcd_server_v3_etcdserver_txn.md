# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/txn` (3b)


## from 2c

What the request path (2c) needs of `etcdserver/txn` (3b):

1. **`txn.Range(ctx, lg, kv, r, true)`** over the member's store (`s.KV()`): the answer `RangeAns`
   that W0's `RangeReq.answers` allows at the store's revision `readRev` of the member's applied
   history `histAt N k σ` (`k` the applied point when the read transaction began), its header
   revision `σ.kv.rev`; or `ErrCompacted`/`ErrFutureRev` as `RangeReq.revErr`. The reply message
   owned (`rangeRespOwn`), the request read-only. Used by: `Range.spec`, `RangeStream.spec`.
2. **`txn.Txn(..., s.KV(), s.lessor, false)`** for a read-only transaction: `TxnRun` at the member's
   store (no events), the reply `txnRespOwn`; `IsTxnReadonly(r)` is `t.readonly`, `IsTxnSerializable`
   is `t.serializable`. Used by: `Txn.spec`.
3. **`txn.Count(ctx, lg, kv, key, end, rev)`** (a stream's remaining count) at the pinned revision.

## from 3c

1. **`checkLease`** (`txn/put.go:80-88`): `lessor.Lookup.spec` (`Spec/go_etcd_io/etcd/server/v3/lease/`)
   takes `isLessor` and a lower bound `Lease.lessorLb γl i`; at the writer's own state (the apply
   thread holds `lessorState γl n ls`: pass `lessorAt γl n ls`, `lessorState_at`) it answers from
   `ls` exactly (`lessorState_le`, `lessorAt_agree`): `nil` iff `ls.leases id = none`. The txn
   layer's write specs thread `lessorState` to mvcc's put (which `Attach`es, panicking on an error:
   the lease checked live at the same state). Used by: `lessor.Attach.spec`'s callers (3e).


## from 3a

The backend applier (3a: `applierV3backend.{Put,Range,DeleteRange,Txn}`) calls `txn.Put(ctx, lg,
lessor, kv, p)`, `txn.Range(ctx, lg, kv, r, true)`, `txn.DeleteRange(ctx, lg, kv, dr)`, `txn.Txn(ctx,
lg, rt, sharedBuf, kv, lessor, skip)` on the apply thread, the store exclusively its (3a's `kvSt kv h`,
the lessor's `lessorSt`), the backend's post-lock hook running with the apply thread's lent `R`
(`kvOk kv R`). Needed:
1. **Each is a step of W0's model at the store** (for an admitted request: `Apply.reqAdmitted`): the
   put/delete/transaction's `kvStep` success or its own errors (`ErrLeaseNotFound`,
   `ErrKeyNotFound`, `ErrFutureRev`, `ErrCompacted`), the store moved to the step's history, the
   reply message (`EtcdWire.*RespOwn`) with the header's revision; **deterministic**: Go's answer is
   a function of the store and the request (the sort of a range is `sort.Sort`'s, a fixed function of
   its input: 3a's `opStep_fun`).
2. `skipRangeExecution`: the ranges' answers empty with the revision kept (3a's `skipRanges`).
3. No panic for an admitted request: a write transaction's execution error (`lg.Panic`, `txn.go:91`)
   is unreachable after `checkTxn` passed.
4. `ApplySecObserve`, `WarnOfExpensiveRequest`, `WarnOfFailedRequest` (`dispatch`'s defer): safe with
   a logger and the request's stringer (any response, any error).
Used by: `applierV3backend.{Put,Range,DeleteRange,Txn}.spec`, `uberApplier.dispatch.spec`.
```go
return mvcctxn.Txn(context.TODO(), a.options.Logger, rt, a.options.TxnModeWriteWithSharedBuffer,
	a.options.KV, a.options.Lessor, skipRangeExecution)                       // backend.go:62-64
```
