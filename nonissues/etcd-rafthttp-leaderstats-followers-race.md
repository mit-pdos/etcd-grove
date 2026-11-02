---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#1317 pr merged: an earlier (2015) race on the leader stats' `Followers`, in old cluster-store code; different code path
  - etcd-io/etcd#2274 pr merged: added `removePeer`'s delete of the follower's stats, the unlocked write
  - etcd-io/etcd@692b3c4cd: "server: Remove most of V2 API": removed `JSON`'s only caller (`/v2/stats/leader`) from main; release-3.6 has none either, release-3.5 still serves it under `--enable-v2`
blocks-proof: no
---

# release-3.5: the v2 leader stats endpoint races rafthttp's peer changes on `LeaderStats.Followers`

On release-3.5 with the deprecated `--enable-v2`, a `/v2/stats/leader` request marshals the
leader stats' `Followers` map without its lock while rafthttp adds or removes a peer, a data race
that Go's map checks can turn into `concurrent map iteration and map write`.

**Why not an issue:** not on `main`, release-3.6 or the pin, where `LeaderStats.JSON`, the one
reader outside the transport's lock, has no caller and both writers hold the transport's lock;
only release-3.5 with `--enable-v2` races. No test, found by code reading.

## Proof

no: outside the verified code (rafthttp and v2stats are names-only; the stats map is not modeled).

## Notes

Moved to non-issues on 2026-10-26 (the user's decision). Move it back if a release-3.5 fix is
wanted: `JSON` marshalling under the lock and a `LeaderStats.RemoveFollower` taking the lock.
