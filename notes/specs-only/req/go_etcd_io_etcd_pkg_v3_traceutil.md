# Requirements on `go.etcd.io/etcd/pkg/v3/traceutil` (4b)


## from 2c

`traceAt tr` (provisional in `ApiReq.lean`): a `*traceutil.Trace` (or `nil`) whose methods
(`GetStartTime`, `SetStartTime`, `InsertStep`, `LogIfLong`, `Step`, `AddField`) never panic; and
`EnsureTrace`, `Get` from a context (any context: `Get` of one with none returns `TODO()`'s).
