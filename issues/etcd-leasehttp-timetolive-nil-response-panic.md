---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# leasehttp: a follower's `LeaseTimeToLive` crashes the member when the leader's peer URL answers 200 with an empty body

A follower serving `LeaseTimeToLive` forwards it to the leader's peer URLs; if one of them answers
`200` with a body that is not a full TimeToLive reply (an empty body, or another message), the
follower dereferences a nil pointer on the gRPC handler's goroutine and the member exits. etcd's own
lease handler always sets the reply, so it takes something other than an etcd member at a peer URL
(a proxy or load balancer, a misconfigured endpoint) or a corrupted reply.

**Expected:** a malformed reply should be an error, as a non-200 status or an unmarshal failure is
in [`TimeToLiveHTTP`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/lease/leasehttp/http.go#L260-L273),
which `leaseTimeToLive`'s loop then treats like any other failed URL.

**Impact:** a member serving a client's `TimeToLive` while it is a follower, in a deployment
where a peer URL is answered by something that is not etcd. Between etcd members the reply is
always well formed. Any release with the follower forwarding path.

**Reproduction:** `TestTimeToLiveHTTPEmptyOKReply` in
[`issues/etcd-leasehttp-timetolive-nil-response-panic/timetolive_nil_response_test.go`](etcd-leasehttp-timetolive-nil-response-panic/timetolive_nil_response_test.go),
copied into `server/lease/leasehttp` at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5
(2026-11-02), go1.27.3 linux/amd64. It calls `TimeToLiveHTTP` as
[`leaseTimeToLive`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L676-L691)
does on a follower, against an `httptest` server answering `200`:

```
$ go test ./lease/leasehttp -run '^TestTimeToLiveHTTPEmptyOKReply$' -count=1
--- FAIL: TestTimeToLiveHTTPEmptyOKReply (0.02s)
    timetolive_nil_response_test.go:38: TimeToLiveHTTP panicked: runtime error: invalid memory address or nil pointer dereference
FAIL
FAIL	go.etcd.io/etcd/server/v3/lease/leasehttp	0.083s
```

**Cause:** `TimeToLiveHTTP` unmarshals the reply into a `LeaseInternalResponse` and reads
`lresp.LeaseTimeToLiveResponse.ID`
([L270-L276](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/lease/leasehttp/http.go#L270-L276))
without checking that the field is set; an empty body unmarshals to a message without it. The call
runs on the gRPC handler's goroutine (`EtcdServer.LeaseTimeToLive` → `leaseTimeToLive`), and etcd
installs no recovery interceptor, so the process exits.

## Proof

no: the trust-boundary contract `EtcdServer.leaseTimeToLive.spec`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`) takes the premise
`leasePeersOk` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseRead.lean`): whatever answers the
leader's peer URLs answers `200` only as etcd's lease handler does, which etcd's members meet.

## Fix

Not written. `if lresp.LeaseTimeToLiveResponse == nil { return nil, fmt.Errorf("lease: empty
TimeToLive response") }` before the `ID` check; adding `|| lresp.LeaseTimeToLiveResponse.Header ==
nil` also fixes `issues/etcd-leasehttp-timetolive-nil-header-panic.md`.

## Notes

The contract once stated this assumption in prose only, and the axiom review of 2026-11-02
(`notes/axiom-review/lease-ttl-id.md`) reached the panic with a whole program through
`EtcdServer.LeaseTimeToLive` on a one-member cluster whose own peer address answered `200` (the call
made before the first election, so the member forwards to itself); the premise was added then. The
same class as `issues/etcd-rafthttp-stream-dial-bad-server-version-panic.md` (a non-etcd server at
a peer URL crashes the member).
