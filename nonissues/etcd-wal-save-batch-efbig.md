---
upstream: none
checked: 2026-11-19
links:
blocks-proof: yes
---
# etcd: one `Save` of a huge `Ready` writes past the WAL file-size limit, and the raft loop exits

`wal.Save(st, ents)` writes every entry record, then the hard state, into the tail segment, and only then
checks whether to cut (`curOff < SegmentSizeBytes`)
([wal.go](https://github.com/upamanyus/etcd/blob/34dea163a/server/storage/wal/wal.go#L1104-L1143)). The raft
loop saves a whole `Ready` in one call, `r.storage.Save(rd.HardState, rd.Entries)`, and exits on an error
(`r.lg.Fatal("failed to save Raft hard state and entries")`,
[raft.go](https://github.com/upamanyus/etcd/blob/34dea163a/server/etcdserver/raft.go#L264-L266)). A `Ready`'s
`Entries` are all of raft's unstable entries, and etcd configures no `MaxUncommittedEntriesSize`
([bootstrap.go](https://github.com/upamanyus/etcd/blob/34dea163a/server/etcdserver/bootstrap.go#L580-L592)),
so raft does not bound them: proposals accumulate while the raft loop is busy. If one batch's records
pass ext4's `s_maxbytes` (16 TiB) the write fails (`EFBIG`) and the member exits.

**Why not an issue:** the batch must be held in memory at once, so it needs more than 8 TiB of RAM in one
process. Code reading only; no test.

## Proof

yes: layer 1's `WAL.Save.spec` takes `walCov Sio → saveRoom Mr hs es ≤ walFreshRoom` (the batch fits the
room a fresh tail leaves, about 8 TiB), so the server's `Save` law needs it, and the raft loop has no fact
bounding a `Ready`'s entries' total size (each is bounded, `entSizeOk`, not their number). Open at the
wal-link L3 stop of 2026-11-19 (`notes/wal-link-handoff.md`): a fix in the fork, an error arm the raft loop's
`lg.Fatal` covers, or a premise.
