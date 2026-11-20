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
bounding a `Ready`'s entries' total size (each is bounded, `entSizeOk`, not their number). Resolved by the fork fix below: layer 1's
room premise is gone; a batch that passes the new check fits (`saveRoom … ≤ 2^42 + 2^32 + 64 ≤ walFreshRoom`).

## Fix

Fixed on the goosed fork (2026-11-19, the user's approval via etcd-grove-03): fork fix 0009
(`notes/wal-fsext-fork/README.md`; upamanyus/etcd branch `goose-lean-walfs3-fp9`, `d3feef9bc`): `WAL.Save` sums
`proto.Size(e)+64` over the batch and returns `ErrSaveBatchTooLarge` before `w.mu.Lock()` once the sum passes
`MaxSaveBatchBytes` (`1 << 42`), with nothing written; test `TestSaveBatchTooLarge`. The raft loop still exits
(`lg.Fatal`) on that error, as it did on `EFBIG`, but past 4 TiB instead of 16 TiB and with the WAL untouched.
The proof: `WAL.Save.spec`'s refused arm (the share back; the update demanded only for a batch that fits),
`WalPbIn.SizeLaw` (`proto.Size` of an entry, from `proto.SizePb.spec`), and the server's `Save` law's error arm
(the share, the reader token and the update back), which the raft loop's `lg.Fatal` covers.
