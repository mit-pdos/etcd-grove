---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# server: a watch progress interval above about 265 years crashes the member on the first watch

With `--watch-progress-notify-interval` set above about `(2^63-1)·10/11` ns (about 265 years;
`2562047h` is accepted), the random jitter added to the interval overflows it to a negative duration,
and every watch stream's `time.NewTicker` panics, crashing the member on the first `Watch` and again
after every restart. (An interval below 10 ns also panics, in `rand.Int63n`, but only through the
test-only `SetProgressReportInterval`: the configured value is clamped to at least 100 ms.)

**Why not an issue:** an absurd configuration: no deployment sets a progress interval of centuries
(the user's 2026-10 review: skip); a configuration validation gap. The test below is valid otherwise
(the flag's value through the integration framework's member config).

**Test:** `TestWatchHugeProgressNotifyInterval` in
[`nonissues/etcd-watch-progress-interval-overflow/watch_progress_interval_overflow_test.go`](etcd-watch-progress-interval-overflow/watch_progress_interval_overflow_test.go),
copied into `tests/integration/clientv3/watch` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef,
go1.27.3 linux/amd64:

```
$ go test ./integration/clientv3/watch/ -run '^TestWatchHugeProgressNotifyInterval$' -count=1
panic: non-positive interval for NewTicker
	server/etcdserver/api/v3rpc/watch.go:418 +0x125
FAIL	go.etcd.io/etcd/tests/v3/integration/clientv3/watch	0.243s
```

Cause: [`GetProgressReportInterval`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L99-L110)
returns `interval + jitter` unchecked, and `NewWatchServer` clamps the configured interval below but
not above ([L77-L86](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L77-L86)).

## Proof

no: `NewWatchServer.spec` requires a configured interval of at most `2^62` ns (about 146 years;
the interval's resource holds `10 ≤ d ≤ 2^62`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/BaseWatch.lean`), a premise on the configuration
that every real one meets (default 10 minutes) though the flag does not enforce it.

## Notes

Fix if wanted: clamp the interval above in `NewWatchServer` (as below), and compute the jitter as
`rand.Int63n(max(int64(interval)/10, 1))` with a saturating sum.
