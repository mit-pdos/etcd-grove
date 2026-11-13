---
upstream: known
checked: 2026-11-13
links:
  - etcd-io/etcd#22638 issue open: this bug (rafthttp stream connections have no read/write timeouts since v3.5.0)
  - etcd-io/etcd#22639 pr open: the fix (apply timeouts through DialContext)
blocks-proof: no
---

# client/pkg/transport: NewTimeoutTransport never applies its read/write timeouts

A transport from `transport.NewTimeoutTransport` with read and write timeouts never times out a
read or a write: `NewTransport` sets the transport's `DialContext`, `NewTimeoutTransport` then sets
the deprecated `Dial` to its timeout dialer, and net/http uses `DialContext` when both are set, so the
timeout dialer never runs. rafthttp's stream round tripper (`ConnReadTimeout`, `ConnWriteTimeout`,
5s) gets no timeouts on peer connections.

**Reproduction:** `TestNewTimeoutTransportReadTimeout` in
[`issues/etcd-timeout-transport-rw-timeouts-unused/timeout_rw_test.go`](etcd-timeout-transport-rw-timeouts-unused/timeout_rw_test.go),
copied into `client/pkg/transport` at etcd-io/etcd v3.7.3 (`go.etcd.io/etcd/client/pkg/v3@v3.7.3`;
`main` has the same code, checked 2026-11-13), go1.27.3:

```
$ go test ./transport -run TestNewTimeoutTransportReadTimeout
--- FAIL: TestNewTimeoutTransportReadTimeout (3.00s)
    timeout_rw_test.go:66: RoundTrip still blocked 3s after the 100ms read timeout
```

With `tr.DialContext = nil` before the `tr.Dial` assignment the test passes (`i/o timeout` after
100ms).

## Proof

no: a missing timeout is liveness only; `rafthttp.NewRoundTripper`/`newStreamRoundTripper` are
trust-boundary axioms (`http.roundTripperOk`) that promise nothing about timeouts, and no
top-level result depends on one. Found by the axiom review of k8s 7f-4's Addendum T-i (m7).
