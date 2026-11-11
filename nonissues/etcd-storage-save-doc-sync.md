---
upstream: none
checked: 2026-11-11
links:
blocks-proof: no
---
# etcd: Storage.Save's documentation says it blocks until the state is on stable storage, but a commit-only Save does not sync

`serverstorage.Storage`'s comment says "Save MUST block until st and ents are on stable storage"
([storage.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/storage.go#L31)), but the WAL's `Save` syncs only when
`raft.MustSync` says so ([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L1015)): a `Save` that only advances
the commit index, with no entries and the same term and vote, returns before anything is synced.

**Why not an issue:** documentation only. Raft does not need the commit index synced (`MustSync`'s
own comment), and the server relies on nothing more; the interface's comment overstates what its
only implementation does.

## Proof

no: the WAL spec's `Save` law moves the synced mark only on a `MustSync` save
(`walMustSync`), as the code does.
