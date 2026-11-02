---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21829 pr open: same root cause and fix (`serverVersion`/`minClusterVersion` tolerate a malformed header), by someone else; framed as the handler side, not the dialer's crash; needs a rebase, no review
  - etcd-io/etcd#22261 pr open: related: a `v`-prefixed `X-Server-Version` from a custom build fails to parse at release-3.6/3.5 peers (coreos/go-semver), so the parse failure is reachable between etcd builds there
  - etcd-io/etcd#21839 pr merged: the switch to Masterminds/semver/v3, whose `MustParse` still panics on a non-version
blocks-proof: no
---

# rafthttp: a peer's response with a malformed `X-Server-Version` crashes the member that dialed it

When a member dials a peer's raft stream and the response carries an `X-Server-Version` header
that is not a semantic version, the dialing member panics and exits. Between etcd members on
`main` the header is always valid, so it takes a non-etcd server (or a proxy rewriting the header)
at a peer URL; on release-3.6/3.5 a custom build's `v`-prefixed version also triggers it
(etcd-io/etcd#22261).

**Reproduction:** `TestStreamReaderDialBadServerVersion` in
[`issues/etcd-rafthttp-stream-dial-bad-server-version-panic/stream_dial_bad_version_test.go`](etcd-rafthttp-stream-dial-bad-server-version-panic/stream_dial_bad_version_test.go),
copied into `server/etcdserver/api/rafthttp` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 linux/amd64. It
dials through the package's own harness, as `TestStreamReaderDialHttpError` does:

```
$ go test ./etcdserver/api/rafthttp -run TestStreamReaderDialBadServerVersion -count=1
--- FAIL: TestStreamReaderDialBadServerVersion (0.00s)
    zz_dial_test.go:30: dial panicked: invalid semantic version
FAIL	go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp	0.017s
```

**Cause:** [`streamReader.dial`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/rafthttp/stream.go#L612)
calls [`serverVersion`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/rafthttp/util.go#L148-L155),
which is `semver.MustParse` of the header. `dial` runs on the stream reader's goroutine, outside
any HTTP handler, so nothing recovers the panic.

## Proof

no: the proof constrains the headers a member's handler commits (a parsable version,
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__dial.lean`), which etcd's
own members meet; only a non-member at a peer URL reaches the panic.

## Fix

`serverVersion` (and `minClusterVersion`) parse with `semver.NewVersion` and `dial` turns an error
into a failed dial, as etcd-io/etcd#21829 does.
