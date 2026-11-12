# Requirements on Go's `context` (W0's `SpecPlan/Spec/context/Api.lean`)

## from R1

Raft's node methods (`node.Propose`, `Step`, `ProposeConfChange`, `Campaign`, `ForgetLeader`,
`ReadIndex`, `TransferLeadership`: `SpecPlan/Spec/go_etcd_io/raft/v3/node__*.lean`) take any context
(`Context.ctxOk ctx`: rafthttp passes `context.TODO()`) and wait on it in a `select`
(`node.stepWithWaitOption`, node.go:519-520, 535-536, 545-546):

```go
select {
case n.recvc <- m:
	return nil
case <-ctx.Done():
	return ctx.Err()
case <-n.done:
	return ErrStopped
}
```

They need, beside `Err.spec`/`ErrDone.spec`:
- **`Context.Done.spec`**: under `ctxOk ctx`, `ctx.Done()` returns either `nil` (a context never
  done: `Background()`, `TODO()`) or a channel `ch` with a persistent receive contract;
- **`Context.doneRecv.spec`**: a receive on that channel (as a `select` case: Perennial's `recvAu`,
  or a bundle the select rule accepts) completes only once the context is done, and gives
  `ctxDone ctx`; a `nil` channel's case never fires (Perennial's select rule for nil channels).

Used by: `node.stepWithWaitOption.spec`'s sketch, hence every `node.*` spec with a context (their
post's context arm `Context.ctxDone ctx ∗ isCtxErr err`, `nodeErr`).

## from 1b

1. **`context.WithCancel` over any context** (`ctxOk`, not only Perennial's `isContext`): the
   client's watch stream runs on `context.WithCancel(&valCtx{inctx})` (`newWatcherGRPCStream`), whose
   parent is the package's own type `valCtx` (never done: `Done` the package's never-closed
   `valCtxCh`, `Err` `nil`, `Value` the caller's context's: 1b's `valCtx_ctxOk.spec`). Needed: a
   spec of `WithCancel(parent)` for a `ctxOk` parent giving a `ctxOk` child that is done once
   `cancel` is called or the parent is done, and `cancel` callable any number of times
   concurrently (the watcher's `close` and `closeStream` both call it).
   ```go
   ctx, cancel := context.WithCancel(&valCtx{inctx})
   ```
   Used by: `watcher.newWatcherGRPCStream.spec`, `watchGRPCStream.close.spec`,
   `watcher.closeStream.spec`; through them `watcher.Watch.spec`.
2. **`ctx.Done()` in a `select`** on any `ctxOk` context (W0's bundle gives `Err`; `Watch`,
   `RequestProgress`, `serveSubstream` and `sendCloseSubstream` select on `Done()`, and
   `ReqWatchSelect` does): the bundle should include `Done`'s channel as a receive case (R1's
   request above is the same need).
   (Update, after W0's round 1: `Context.WithCancel.spec`, `ctxChild`, `cancelOk`, `Done.spec`,
   `doneRecv.spec` cover items 1 and 2; 1b's sketches cite them.)

## from 3b

**`TODO()` and `Background()` are never done**: their result `ctx` has `Context.ctxDone ctx ⊢ False`
(their `Done()` is `nil`). The apply thread passes `context.TODO()` to `txn.Txn`, whose writing
transactions panic on a context error (`txn.go:91`): `Txn.spec` takes `Context.ctxDone ctx -∗ False`
for a write. Used by: `Txn.spec`, `txn.spec` (3a's `applierV3backend.Txn`).

## from 4b

`Context.TODO.spec` returns an unnamed `ctxOk ctx`; the apply layer's traces are made at
`context.TODO()` (`TraceUtil.EnsureTrace(context.TODO(), ...)`), whose `ctxTraceIs_todo` and
`OtelTrace.ctxSpanOk_todo` are stated at Perennial's `context.todoCtxVal`. Please name the value
(`ctx = GoInterface.ok context.todoCtxVal`, as `ctxOk_background` names `backgroundCtxVal`), or give a
law that `TODO()`'s context carries no value at any key.
