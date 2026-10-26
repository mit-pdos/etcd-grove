---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#1317 pr merged: an earlier (2015) race on the leader stats' `Followers`, in old cluster-store code; different code path
  - etcd-io/etcd#2274 pr merged: added `removePeer`'s delete of the follower's stats, the unlocked write
  - etcd-io/etcd@692b3c4cd: "server: Remove most of V2 API": removed `JSON`'s only caller (`/v2/stats/leader`) from main; release-3.6 has none either, release-3.5 still serves it under `--enable-v2`
---

> Moved to `issues/nonissues/` on 2026-10-26 (the user's decision, for now): not an issue on etcd's `main`, release-3.6 or the pin, where `LeaderStats.JSON` has no caller and both writers of the map hold the transport's lock; only release-3.5 with the deprecated `--enable-v2` races. Move it back if a 3.5 fix is wanted.

# release-3.5: the v2 leader stats endpoint races rafthttp's peer changes on `LeaderStats.Followers`

**Status**: a data race only on etcd's release-3.5 with the deprecated `--enable-v2` (code
reading, not reproduced): a `/v2/stats/leader` request marshals the `Followers` map without the
stats lock while a peer is added or removed; with Go's map checks it can end the process
(`concurrent map iteration and map write`). Not a bug on `main`, release-3.6 or the pin (rechecked
2026-10-26): there `JSON`, the one reader outside the transport's lock, has no caller (the v2 API
went with 692b3c4cd), and both writers (`Follower` from `AddPeer`, the delete in `removePeer`) hold
the transport's `mu`, so the unlocked delete is latent only. (As first written, 2026-10-24, this
finding claimed the race at the pin, missing that `JSON` is dead there.)

**Where** (etcd at the pin `bc9c3868c` of `etc/goose.py`; the same on `main` `f3221acd1`):
- `server/etcdserver/api/rafthttp/transport.go:342-356`, `removePeer` (from `RemovePeer` and
  `RemoveAllPeers`, under the transport's `mu`): `delete(t.LeaderStats.Followers, id.String())`,
  without `LeaderStats`' lock.
- `server/etcdserver/api/v2stats/leader.go:67-77`, `Follower` (only from `AddPeer`, also under the
  transport's `mu`): reads and inserts into `ls.Followers` under `ls.Lock()`.
- `server/etcdserver/api/v2stats/leader.go:55-64`, `JSON`: copies `ls.leaderStats` under the lock
  but `json.Marshal`s it after `Unlock`; the copy shares the `Followers` map, so the marshal ranges
  over the map without the lock. No caller outside tests at the pin, on `main` or on release-3.6.
- release-3.5: `server/etcdserver/server.go:1635-1640`, `EtcdServer.LeaderStats` returns
  `s.lstats.JSON()`, served by `v2http/client.go:106` (`statsPrefix+"/leader"`, `serveLeader`),
  registered only with `--enable-v2` without `--experimental-enable-v2v3` (whose `fakeStats`
  returns nil; `embed/etcd.go:771-782`).

**What happens** (release-3.5, `--enable-v2`): `removePeer` is reached from `applySnapshot`
(`s.r.transport.RemoveAllPeers()`) and from a member removal (`RemovePeer`), `Follower`'s insert
from a member addition, and `JSON` from the leader's `/v2/stats/leader`. A stats request during
any of them races the map; the race detector reports it, and the Go runtime may abort with
`concurrent map iteration and map write`. The marshal also reads each `FollowerStats` without that
follower's own lock, which the pipeline holds while updating it: a second race of the same request.

**Expected**: the stats map guarded by `LeaderStats`' lock for every access.

**How the proof handles it**: outside the verified code: rafthttp and v2stats are names-only, the
stats endpoint is not served in the verified examples, and the stats map is not modeled
(`rafthttp.Transport.RemoveAllPeers.spec`'s docstring,
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__RemoveAllPeers.lean`).

**Possible fixes**: on release-3.5, `JSON` marshalling under the lock (or a copied map, each
follower's stats copied under its lock) and a `LeaderStats.RemoveFollower(name)` taking
`ls.Lock()`, used by `removePeer`. On `main`, nothing is broken; `JSON` could go with the rest of
v2 stats. Worth a release-3.5 PR only if 3.5 still takes such fixes.

**Found**: 2026-10-24, writing `RemoveAllPeers`' trust-boundary axiom (D22 receiver epochs, S8c).
