---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---
# wal: a segment's name wraps to 0 after a record of index 2^64-1

A cut names the new segment `walName(seq+1, index)` with `index = w.enti+1` in `uint64`
(`cut`, [wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go); at the
etcd pin `0b50f0426`, `max(w.enti, w.snapi)+1`). After an entry or a snapshot record of index
`2^64-1` the name's index is 0. `searchIndex` takes the last segment named at or below an index, so
`Open` at a low index selects the wrapped segment: it locks only from there (`ReleaseLockTo` likewise
keeps only the tail), a purge may delete earlier segments the WAL still needs, and with a `(0,0)`
snapshot record after the wrap, `Open(0)` followed by `ReadAll` succeeds reading only the wrapped
segment (fewer entries than the WAL holds).

**Why not an issue:** raft never reaches index `2^64-1` (an index grows by one per entry), and etcd
writes the WAL with raft's indices: the entries and snapshot of raft's `Ready`, etcdserver's own
`SaveSnapshot` at the applied index, and `etcdutl` restore's snapshot record at the restored index;
the WAL's own API documents no index range. Shown with Go
tests at the fork: `TestW4a2NameWrapReleaseLockTo`, `TestW4a2NameWrapUnlocksGuardedRecord`
(`/shared/tmp/wal-spec/w4a2/tests/w4a2_wrap_test.go`) and the W4a.2 review's
`TestReviewWrapZeroReadAllSucceeds`, `TestReviewWrapZeroReadAllFewerEntries`
(`/shared/tmp/coord-81/wal-w4a2-review/purge-restart/etcd/server/storage/wal/zz_review_wrap0_test.go`).

## Proof

no (after WAL W4a.2 revisions 1 and 2): `(*WAL).Save` and `(*WAL).SaveSnapshot`'s trust-boundary specs
take indices below `2^64-1` (`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`,
`WAL__SaveSnapshot.lean`), and no WAL exists at the start (`absDiskInitOk`), so every history the run
builds from `Create` lacks the index, and `ReadAll`'s read of the whole
history and the purge bounds hold. Before it, the wrap made `ReadAll`'s success arm and the purge
bounds false (findings F-W4a2-1 and the review's B1, `notes/decisions.md`, "WAL W4a.2"). A caller
(the WAL tester, later the server) discharges the premise from raft's index bound.

## Notes

Found by WAL W4a.2 (2026-11-12) and its Freeze review.
