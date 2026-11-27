---
upstream: none
checked: 2026-11-27
links: []
blocks-proof: no
---
# etcdserver: a restart re-adds a transport peer for a member add that the cluster rejected

When a member restarts, it replays the WAL entries at or below its backend's consistent index without
validating conf changes. A member add that was rejected when first applied therefore reaches
`transport.AddPeer`. Two such rejections are a peer URL already in use and the learner limit. The
restarted member then keeps a peer for an ID that is not a member, until its next restart.

**Why not an issue:** found by code reading, no test. The effect is extra connection attempts and log
noise: the remote end refuses a mismatched member ID, and raft never sends to an ID outside its
configuration. Neither safety nor client-visible.

## Cause

`apply` marks entries `≤ ci` `ApplyV2storeOnly` (`server/etcdserver/server.go`, `apply`).
`ValidateConfigurationChange` returns nil for them (`api/membership/cluster.go`, upstream since
fdedec1ed "Remove v2 store"; the replay's `shouldApplyV3` gate since 25a5bb287). `applyConfChange` then
skips raft but still runs the transport call: `AddPeer` for an add that is not a promotion.
`AddMember` itself is a no-op under `ApplyV2storeOnly`. A rejected remove or update reaches only
`RemovePeer` or `UpdatePeer` of an absent peer, which do nothing.

## Proof

no: the transport's peer set is not part of any result's statement.

## Notes

Found while listing what our fork's keep guard skips
([`etcd-keepguard-raft-confstate-stale`](etcd-keepguard-raft-confstate-stale.md), section 3). The fix
would be to skip the transport call when the replayed change would have failed validation. That
validation needs the membership at the entry's index, which the replay does not have.
