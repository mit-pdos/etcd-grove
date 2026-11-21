# `txn.ApplySecObserve` and `v2stats.ServerStats.{Recv,Send}AppendReq`: premises missing (prove-etcdserver, 2026-11-20)

Found by reading the code at the etcd fork's pin (goose-lean, `etc/goose.py`'s project `etcd`) and
client_golang v1.24.1 (etcd `server/go.mod`), not by the `axiom` skill: no Lean counterexample was built.

## `txn.ApplySecObserve.wp_proof`: **false as stated, fixed (and proved)**

`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/ApplySecObserve.lean` held for every `version, op` with
only `isPkgInit`. `server/etcdserver/txn/metrics.go:59-61`:

```go
func ApplySecObserve(version, op string, success bool, latency time.Duration) {
	applySec.WithLabelValues(version, op, strconv.FormatBool(success)).Observe(float64(latency.Microseconds()) / 1000000.0)
}
```

`HistogramVec.WithLabelValues` panics when `GetMetricWithLabelValues` errs (`histogram.go:1263`),
which it does on a label value that is not valid UTF-8 (`validateLabelValues`, `labels.go:166`). So
`txn.ApplySecObserve("\xff", "op", true, 0)` panics while the axiom proved it returns.

Fix: the premise `⌜utf8Valid version ∧ utf8Valid op⌝`. Its callers, the apply thread's `dispatch`
(`uber_applier.go:98`, `txn.ApplySecObserve("v3", op, ...)`, `op` one of the literal operation names),
discharge it by `decide` (`apply/DispatchKVL.lean`, `DispatchAdmin.lean`, `uberApplier__dispatch.lean`).
The function is now translated and proved over `WithLabelValues`' spec, with `applySec`'s label names
in the txn package's fact (`txnInit`); `RangeSecObserve` likewise (its only label is `FormatBool`'s,
ASCII: its spec was true).

## `v2stats.ServerStats.RecvAppendReq.wp_proof`, `SendAppendReq.wp_proof`: **false as stated, recorded, not fixed**

Both specs take `st ≠ null` only. `server/etcdserver/api/v2stats/server.go:91-128`: each locks the
stats and calls `ss.recvRateQueue.Insert(...)` / `ss.sendRateQueue.Insert(...)`; `queue.go:62-63`,
`func (q *statsQueue) Insert(p) { q.rwl.Lock(); ...`, dereferences `q`. The queues are allocated only
by `NewServerStats`; `ServerStats` is exported, so `(&v2stats.ServerStats{}).RecvAppendReq("a", 1)`
panics (nil pointer dereference) while the axioms prove it returns. (`BecomeLeader` and
`FollowerStats.Succ`/`Fail` do not touch a queue: a zero value returns; their specs hold, though none
of these specs owns the lock's protocol either.)

The premise needed: a persistent `v2stats.isServerStats st` (queues allocated, the stats' and queues'
locks), in `NewServerStats`' post (an axiom: the type has an anonymous struct field, `LeaderInfo`,
which Goose does not translate), required by `RecvAppendReq` and `SendAppendReq`. The callers are
`EtcdServer.Process` (the server's `stats`) and rafthttp's `Transport.Send` (the transport's
`ServerStats` field), so the fact must be threaded through the server's construction and the
transport's invariants (rafthttp's files, another group's on 2026-11-20): left for that change.
Not reachable from etcd: etcd only passes `NewServerStats`' result.
