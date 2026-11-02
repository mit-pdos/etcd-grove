---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# v3rpc: a follower's `LeaseTimeToLive` crashes the member when the leader's peer URL replies without a response header

A follower serving `LeaseTimeToLive` forwards it to the leader's peer URLs; if one of them answers
`200` with a TimeToLive reply for the asked lease but without its response header, the follower
accepts it and the gRPC handler panics (`unexpected nil resp.Header`), and the member exits.
etcd's own lease handler always sets the header, so it takes something other than an etcd member at
a peer URL (a proxy or load balancer, a misconfigured endpoint) or a corrupted reply.

**Expected:** a malformed reply should be an error, as a non-200 status is in
[`TimeToLiveHTTP`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/lease/leasehttp/http.go#L260-L268),
which `leaseTimeToLive`'s loop then treats like any other failed URL.

**Impact:** a member serving a client's `TimeToLive` while it is a follower, in a deployment
where a peer URL is answered by something that is not etcd. Between etcd members the header is
always set. A sibling of `issues/etcd-leasehttp-timetolive-nil-response-panic.md` (there the reply
lacks the whole TimeToLive response), with the same fix.

**Reproduction:** `TestLeaseTimeToLiveForwardedReplyWithoutHeader` in
[`issues/etcd-leasehttp-timetolive-nil-header-panic/lease_timetolive_nil_header_test.go`](etcd-leasehttp-timetolive-nil-header-panic/lease_timetolive_nil_header_test.go),
copied into `server/etcdserver/api/v3rpc` at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5
(2026-11-02), go1.27.3 linux/amd64. Its `LeaseServer`'s lessor does what
[`leaseTimeToLive`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L676-L691)
does on a follower (`leasehttp.TimeToLiveHTTP` to the peer URL, then its
`LeaseTimeToLiveResponse`), against an `httptest` server answering `200` with
`LeaseInternalResponse{LeaseTimeToLiveResponse: {ID: 1}}`:

```
$ go test ./etcdserver/api/v3rpc -run '^TestLeaseTimeToLiveForwardedReplyWithoutHeader$' -count=1
--- FAIL: TestLeaseTimeToLiveForwardedReplyWithoutHeader (0.03s)
    lease_timetolive_nil_header_test.go:68: LeaseTimeToLive panicked: unexpected nil resp.Header
FAIL
FAIL	go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc	0.058s
```

**Cause:** `TimeToLiveHTTP` checks only the reply's `ID`
([L270-L277](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/lease/leasehttp/http.go#L270-L277)),
`leaseTimeToLive` returns its `LeaseTimeToLiveResponse` as is, and
[`LeaseServer.LeaseTimeToLive`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/api/v3rpc/lease.go#L62-L76)
calls `ls.hdr.fill(resp.Header)`, which
[panics on a nil header](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/api/v3rpc/header.go#L53-L56).
The handler runs on the gRPC goroutine, and etcd installs no recovery interceptor.

## Proof

no: the trust-boundary contract `EtcdServer.leaseTimeToLive.spec`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`) gives a non-nil
header under the premise `leasePeersOk` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseRead.lean`:
the leader's peer URLs answer `200` only as etcd's lease handler does, header set), which etcd's
members meet; the gRPC handler's proof needs it for `fill` (`notes/lease-grpc-plan.md`).

## Fix

Not written. In `TimeToLiveHTTP`, after the unmarshal: `if lresp.LeaseTimeToLiveResponse == nil ||
lresp.LeaseTimeToLiveResponse.Header == nil { return nil, fmt.Errorf("lease: malformed TimeToLive
response") }` (fixes both siblings).

## Notes

The test's lessor replays `leaseTimeToLive`'s two follower lines instead of running an
`EtcdServer`: reaching them for real needs a member whose leader's peer URL is not an etcd member
(the axiom review's program, `notes/axiom-review/lease-ttl-id.md`, did it for the sibling with a
one-member cluster before its first election).
