---
upstream: unchecked
checked: 2026-10-26
links: []
---

# rafthttp: a raft request with a malformed `X-PeerURLs` header from a non-peer id panics its handler

- **Status**: a reachable panic on network input (the peer port), recovered by `net/http` (the
  handler goroutine's panic is logged with its stack and the connection dropped), so not a process
  crash with etcd's own listeners; a robustness bug: `AddRemote` treats a request header as
  trusted configuration. Found while specifying the handlers' `AddRemote` on a live transport
  (D43 "M5c carried out").
- **Where** (the fork at `c00a2dc06`, `goose-lean-learnerfix`):
  `server/etcdserver/api/rafthttp/util.go:199-205` `addRemoteFromRequest` passes
  `strings.Split(r.Header.Get("X-PeerURLs"), ",")` to `AddRemote` for any `X-Server-From` that
  parses as an id; the pipeline and snapshot handlers call it on every request after the cluster
  check (`http.go:117,226`), the stream handler for a sender without a peer (`http.go:423`).
  `Transport.AddRemote` (`transport.go:263-290`), for an id that is neither a peer nor a remote,
  calls `types.NewURLs(us)` and on its error `t.Logger.Panic("failed NewURLs", ...)`.
- **What happens**: a POST to `/raft` (or `/raft/snapshot`) with a matching `X-Etcd-Cluster-ID`
  (the handlers return it in every response's header) and server version, `X-Server-From` an id
  that is not a peer (any id, or a member just removed) and `X-PeerURLs` not a list of
  `http(s)://host:port` URLs panics the handler while it holds the transport's write lock (released
  by the deferred `Unlock` on the way out). Reproduction (a test in package `rafthttp`; passes, i.e.
  confirms the panic, at the fork's pin):

  ```go
  func TestAddRemoteFromRequestBadPeerURLsPanics(t *testing.T) {
  	tr := &Transport{
  		Logger:      zaptest.NewLogger(t),
  		ServerStats: stats.NewServerStats("", ""),
  		LeaderStats: stats.NewLeaderStats(zaptest.NewLogger(t), ""),
  		peers:       make(map[types.ID]Peer),
  		remotes:     make(map[types.ID]*remote),
  	}
  	req, _ := http.NewRequest(http.MethodPost, "http://localhost/raft", nil)
  	req.Header.Set("X-Server-From", "5")
  	req.Header.Set("X-PeerURLs", "not a url")
  	defer func() {
  		if r := recover(); r == nil {
  			t.Fatalf("expected a panic")
  		}
  	}()
  	addRemoteFromRequest(tr, req) // panics: "failed NewURLs"
  }
  ```
- **Expected**: input from the network is validated, not trusted: a request whose peer URLs do
  not parse should be ignored (or rejected with `400`), as `checkClusterCompatibilityFromHeader`
  rejects a bad version or cluster id.
- **How the proof handles it**: on the frozen transport (the static mode) every member is a peer,
  so `AddRemote` returns before `NewURLs` (`AddRemote_frozen`); on a live transport
  (`AddRemote_core`, `Proof/.../api/rafthttp/TransportAdd.lean`) the URL strings are a premise
  (non-empty, plain, owned by the id). The dynamic mode's handler (M8) needs the raft protocol to
  carry that fact of the `X-PeerURLs` header of a request from another member.
- **Possible fixes**: in `AddRemote`, log and return on a `NewURLs` error instead of
  `Logger.Panic` (the remote is only an optimization for answering a not-yet-peer).
- **Found**: 2026-10-26, D43 M5c (the handlers' `AddRemote` on a live transport).
