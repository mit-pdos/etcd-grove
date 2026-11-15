# Requirements on `go.etcd.io/etcd/pkg/v3/traceutil` (4b)


## from 2c

`traceAt tr` (provisional in `ApiReq.lean`): a `*traceutil.Trace` (or `nil`) whose methods
(`GetStartTime`, `SetStartTime`, `InsertStep`, `LogIfLong`, `Step`, `AddField`) never panic; and
`EnsureTrace`, `Get` from a context (any context: `Get` of one with none returns `TODO()`'s).

## from 3b

As 2c's (`Txn.traceAt`, provisional in txn's `Api.lean`, is 2c's `EtcdServer.traceAt`): `EnsureTrace(ctx,
lg, op, fields...)` returns a context carrying a trace and the trace (`traceAt`); `Get(ctx)` a trace
for any context; `Step`, `StepWithFunction` (runs its function once), `AddField`, `StartSubTrace`,
`StopSubTrace` never panic. Used by: every txn entry point.

## from 3e

`Mvcc.traceOwn tr` (provisional in `storage/mvcc/Api.lean`; exclusive): the `*Trace` `tr` (not `nil`)
is the caller's; `tr.Step(msg, fields...)` keeps it (no panic). And `traceutil.TODO()` returns a
fresh non-`nil` trace with `traceOwn`. mvcc's write and read transactions step the trace they were
given (`storeTxnWrite.put`, `rangeKeys`: `tr.trace.Step(...)`); its views and the range deleter call
`traceutil.TODO()` (`kv_view.go`, `kvstore.go:116`). If 2c's provisional `traceAt tr` (persistent) is
what 4b chooses, mvcc can take it instead (a persistent trace whose methods never panic: the
transactions only step it).
```go
tw := wv.kv.Write(traceutil.TODO())                   // kv_view.go:47
tr.trace.Step("range keys from in-memory index tree") // kvstore_txn.go:108
```
Used by: `KV.Read`, `KV.Write`, `KV.Compact`, `Txn.Range`, `Txn.Put` contracts, the views, `mvccDeleter`.
