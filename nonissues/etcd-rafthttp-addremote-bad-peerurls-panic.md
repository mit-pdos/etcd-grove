---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# rafthttp: a raft request with a malformed `X-PeerURLs` header from a non-peer id panics its handler

A POST to a member's `/raft` (or `/raft/snapshot`) with the cluster's id, an `X-Server-From` that
is not a peer and an `X-PeerURLs` that does not parse makes `Transport.AddRemote` call
`Logger.Panic("failed NewURLs")`. `net/http` recovers the handler's panic: the member logs a stack
trace and drops the connection, and stays up.

**Why not an issue:** no harm beyond a log entry: the member does not exit, holds no lock after
the panic (the deferred unlock runs) and the request is dropped, as a rejected one would be; and
only a sender that is not an etcd member (with a client certificate, when peer TLS is on) can send
such a header.

## Proof

no: the raft protocol the proof states says a member's `X-PeerURLs` is its directory URLs, which
`setPeerURLsHeader` proves of the sender, so a member's request never reaches the panic; a
request from outside the cluster is outside the model.

## Notes

Test: `TestPipelineHandlerBadPeerURLs` in
[`etcd-rafthttp-addremote-bad-peerurls-panic/pipeline_bad_peerurls_test.go`](etcd-rafthttp-addremote-bad-peerurls-panic/pipeline_bad_peerurls_test.go)
(package `rafthttp`, through `pipelineHandler` on an `httptest` server) fails at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-11-01): the server logs `http: panic
serving ...: failed NewURLs` and the client gets `EOF`. The fix would be to log and return on
`NewURLs`'s error in `AddRemote` (the remote is only an optimization for answering a not-yet-peer).
Upstream search 2026-11-01 (`X-PeerURLs NewURLs`): nothing.
