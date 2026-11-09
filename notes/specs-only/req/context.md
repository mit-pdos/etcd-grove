# Requirements on Go's `context` (W0's `Spec/context/Api.lean`)

## from R1

Raft's node methods (`node.Propose`, `Step`, `ProposeConfChange`, `Campaign`, `ForgetLeader`,
`ReadIndex`, `TransferLeadership`: `Spec/go_etcd_io/raft/v3/node__*.lean`) take any context
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
