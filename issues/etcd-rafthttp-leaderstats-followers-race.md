---
upstream: unchecked
checked: 2026-10-24
links: []
---

# rafthttp's peer removal writes `LeaderStats.Followers` without the stats lock

**Status**: a data race (code reading, not reproduced): two writers and a reader of the same map
without a common lock; with Go's map checks it can end the process (`concurrent map iteration and
map write`).

**Where** (etcd at the pin `bc9c3868c` of `etc/goose.py`):
- `server/etcdserver/api/rafthttp/transport.go:342-356`, `removePeer` (from `RemovePeer` and
  `RemoveAllPeers`, under the transport's `mu`): `delete(t.LeaderStats.Followers, id.String())`,
  without `LeaderStats`' lock.
- `server/etcdserver/api/v2stats/leader.go:67-77`, `Follower` (from `AddPeer`/`startPeer`): reads and
  inserts into `ls.Followers` under `ls.Lock()`.
- `server/etcdserver/api/v2stats/leader.go:55-64`, `JSON`: copies `ls.leaderStats` under the lock
  but `json.Marshal`s it after `Unlock`; the copy shares the `Followers` map, so the marshal ranges
  over the map without the lock (racing `Follower`'s insert too, independently of `removePeer`).

**What happens**: `removePeer` is reached from `applySnapshot` (`s.r.transport.RemoveAllPeers()`,
`server.go`), from a member removal (`RemovePeer`), and `JSON` from the v2 stats endpoint
(`/v2/stats/leader`, the leader's). A stats request while a snapshot is applied or a member is
removed (or added: `Follower`'s insert) races the map; the race detector reports it, and the Go
runtime may abort with `concurrent map iteration and map write`.

**Expected**: the stats map guarded by `LeaderStats`' lock for every access.

**How the proof handles it**: outside the verified code: rafthttp and v2stats are names-only, the
stats endpoint is not served in the verified examples, and the stats map is not modeled
(`rafthttp.Transport.RemoveAllPeers.spec`'s docstring,
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__RemoveAllPeers.lean`).

**Possible fixes**: a `LeaderStats.RemoveFollower(name)` taking `ls.Lock()`, used by `removePeer`;
and `JSON` marshalling under the lock (or a copied map).

**Found**: 2026-10-24, writing `RemoveAllPeers`' trust-boundary axiom (D22 receiver epochs, S8c).
