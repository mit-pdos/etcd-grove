---
upstream: none
checked: 2026-11-18
links:
blocks-proof: yes
---
# etcd: snapshot records written between two entry-writing saves grow the WAL's tail file without a cut, up to the file-size limit

`wal.SaveSnapshot` appends its record to the tail segment and syncs; unlike `wal.Save` it never cuts
([wal.go](https://github.com/upamanyus/etcd/blob/8c28a4296/server/storage/wal/wal.go#L1148-L1173); `Save` cuts once
the tail passes `SegmentSizeBytes`, 64 MB). The server writes a snapshot record from its apply thread once per
applied batch when `appliedi - diskSnapshotIndex > SnapshotCount` (or `ForceSnapshot`)
([server.go](https://github.com/upamanyus/etcd/blob/8c28a4296/server/etcdserver/server.go#L1251-L1264)), and
raft hands a commit backlog out in batches of at most `MaxCommittedSizePerReady` across `Ready`s whose hard
state and entries are empty (the raft loop's `Save` of those writes nothing, so no cut). So a member applying a
commit backlog of `n` entries writes about `n / max(SnapshotCount+1, entries per batch)` snapshot records into
one tail file. Past ext4's `s_maxbytes` (16 TiB) the write fails (`EFBIG`) and the apply thread panics
(`lg.Panic("failed to save snapshot")`, server.go:2159).

**Why not an issue:** the scale is absurd: about 1.7 * 10^11 snapshot records (a few hundred bytes each)
between two entry-writing saves, i.e. a commit backlog far beyond any member's memory. Code reading only; no
test.

## Proof

yes: the proof cannot exclude the run. Layer 1's `SaveSnapshot` spec (wal-link L1a, option (A), approved
2026-11-17) takes a room budget (`walUsed`, `walSnapBudget = 2^42` bytes of snapshot records since the last
writing `Save`), which the server's invariants were to discharge (L3); the server's history bounds the number
of such records only by the commit backlog, which raft does not bound (`notes/wal-link-handoff.md`, START
HERE 2026-11-18 g). Either the fork's `SaveSnapshot` cuts as `Save` does (a fork fix), or the closed theorems
need a premise excluding the run.

## Fix

Fixed on the goosed fork (2026-11-18, the user's approval via etcd-grove-03): fork fix 0007
(`notes/wal-fsext-fork/README.md`; upamanyus/etcd branch `goose-lean-walfs3-fp`, `f01ae14c9`, with 0008 `34dea163a`: no cut while `w.fp` is nil, `Create`'s call): `SaveSnapshot` cuts once the tail passes `SegmentSizeBytes`, as `Save` does, with the test
`TestSaveSnapshotCuts` (fails before, passes after). The proof then needs no room budget for snapshot
records (wal-link L1a's `walUsed`/`walSnapBudget` go); it does need `walCutPos` to admit a cut right after a
snapshot record (`notes/wal-link-handoff.md`).
