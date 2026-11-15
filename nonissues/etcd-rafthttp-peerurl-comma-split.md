---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# rafthttp: a peer URL with a comma makes the receiver's `AddRemote` panic on every request from that member

`types.NewURLs` accepts a peer URL whose host contains a comma (`http://a,b:2380`: `url.Parse` and
`net.SplitHostPort` both succeed, checked with go1.27.3). rafthttp advertises a member's peer URLs
in the `X-PeerURLs` header joined by `","` (`setPeerURLsHeader`). The receiver splits the header
on `","` (`addRemoteFromRequest`, `util.go:202`; the stream handler, `http.go:423`) and calls
`Transport.AddRemote`. For a sender it does not know as a peer, `NewURLs` then fails on the pieces
and `AddRemote` calls `Logger.Panic("failed NewURLs")`. `net/http` recovers the handler's panic and
drops the connection, so a joining member's requests from such a sender are refused until it
becomes a peer.

**Why not an issue:** no test; found by code reading (2f's round-1 review). A comma in a host is
no valid DNS name or IP literal, and etcd's configuration and real clusters do not use one. The
precondition, that no peer URL contains a comma, is one real configurations meet.

## Proof

no: rafthttp's `Transport.Start.spec` takes `urlsNoComma` of the local URLs (`trCfg`), a fact the
server's membership gives (requested of `client/pkg/v3/types`, `notes/specs-only/req/`).

## Notes

A fix would be to reject a comma in `types.NewURLs` (or to split on `", "`-free encoding, such as a
repeated header). Related: `nonissues/etcd-rafthttp-addremote-bad-peerurls-panic.md` (a
non-member's malformed header).
