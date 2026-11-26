---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# leasehttp: `/leases/internal` dereferences a nil `LeaseTimeToLiveRequest`

The peer handler's `/leases/internal` route (`server/lease/leasehttp/http.go:123` at the examples'
etcd pin `6b942d23f`) unmarshals the body into a `LeaseInternalRequest` and reads
`lreq.LeaseTimeToLiveRequest.ID` without checking that field for nil. A `POST` whose body leaves it
unset (for example a `LeaseKeepAliveRequest`, as `leasehttp.RenewHTTP` sends to any URL: field 1
has the wrong wire type, so it is kept as unknown) makes the handler panic before taking any lock.
`net/http`'s `conn.serve` recovers it (`http: panic serving ...`) and closes the connection; the
client gets `EOF`. The member keeps serving (its lessor usable afterwards). Server-side counterpart
of the client-side `issues/etcd-leasehttp-timetolive-nil-*` findings.

**Why not an issue:** no wrong result or crash of the member: the panic is recovered by the HTTP
server and only that request fails; only a peer (or a program posting to the peer URL) reaches it.
Go evidence: `examples/premisefix/peerforge` (3/3 runs), and the route-B review of `PeerServe_dist`
(2026-11-25, `notes/etcd-dist-plan.md` §17.3).

## Proof

no: `PeerServe_dist` (`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/PeerServeDist.lean`)
covers it as a recovered handler panic.
