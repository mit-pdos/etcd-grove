---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#22594 pr open: passes a positive limit to `rangeEvents`' `ReadTx.UnsafeRange` on the `Key` bucket (`syncWatchers`), a second pager, of recent revisions, with a live read buffer: merged as is, this precondition breaks there (skipped events); its review does not mention it
  - etcd-io/etcd#22264 issue open: what #22594 addresses (the unbounded `syncWatchers` scan); related, different
  - etcd-io/etcd#21986 issue open: the read buffer's merge skips deduplication (a stale single-key read); same code, different bug
  - etcd-io/etcd#22298 pr open: deduplicates the write buffer on every path into the read buffer (#21986); same code, different bug
  - etcd-io/etcd#21987 pr open: deduplicates in writeback before the merge (#21986); related, different
  - etcd-io/etcd#15961 pr closed: `UnsafeRange` with limit 1 when `endKey` is nil; same function, different issue
---

# A limited `ReadTx.UnsafeRange` skips committed entries when the read buffer has some in range

**Status**: an unstated precondition (API documentation). With a positive limit, the read
transaction's range read is a prefix of the range only when its read buffer holds no entry of
the range. etcd's one caller that pages through a bucket with it, `store.restore`, meets that
(the buffer has no `Key` entry when it runs), as far as checked; nothing documents it, so a new
caller, or a change that writes to the `Key` bucket before `restore`, would skip entries silently.
Such a caller is proposed upstream (rechecked 2026-10-26): etcd-io/etcd#22594 (open) bounds
`syncWatchers`' scan by passing a positive limit to `rangeEvents`' `ReadTx.UnsafeRange` on the
`Key` bucket, through the backend's buffered read transaction, over the newest revisions, which are
the ones the read buffer holds: merged as is, an unsynced watcher can miss events. `restore` still
meets the precondition on upstream `main` `f3221acd1` (`kvstore.go:356-372`): `NewStore`
force-commits before it (resetting the buffer), `Restore` runs on a freshly opened snapshot
backend, and `restore` holds `tx.RLock()` across the loop, which writeback and commit wait for. The
other limited range of the `Key` bucket, compaction's (`kvstore_compaction.go:58`), goes through
the batch transaction, which reads bbolt alone.

**Where**: `server/storage/backend/read_tx.go:78` (`baseReadTx.UnsafeRange`) at the fork's pin
(`etc/goose.py`); the interface `UnsafeReader.UnsafeRange` (`read_tx.go:35`) has no comment.
The pager: `server/storage/mvcc/kvstore.go:346-362` (`store.restore`'s chunk loop: the next chunk
starts after the last key returned).

**What happens**: `UnsafeRange(bucket, key, end, limit)` first takes up to `limit` entries of the
range from the read buffer (`buf.Range`); if fewer, it takes `limit - n` entries of the range from
bbolt and returns the bbolt entries followed by the buffer's. For the `Key` bucket the buffer's
entries are the newest revisions, so when bbolt has more than `limit - n` entries in the range,
the result is bbolt's first `limit - n`, then the buffer's `n`: the bbolt entries between them
are not returned, and a caller that continues after the last key returned (`restore`) never sees
them. When the buffer alone has `limit` entries in the range, only they are returned, and every
bbolt entry before them is skipped. (The model: `rtRange` in `Proof/go_etcd_io/etcd/server/v3/storage/backend/Model2.lean`.)
No Go reproduction yet: it needs a backend whose read buffer holds `Key` entries while bbolt holds
more than a chunk of them, and a caller paging through them.

**Expected**: either the doc of `UnsafeRange` says a limited read is a prefix only when the read
buffer has nothing in the range, or the read merges the buffer's and bbolt's entries and limits
the merged list (as `ReadTx.UnsafeRange`'s unlimited read does, by concatenation, when the
buffer's keys all follow bbolt's).

**How the proof handles it**: not yet: the restore plan's R4b (`notes/restore-plan.md`, "R4's
progress") is to extend the backend's range contract (`keyRangeReadSpec`) to a positive limit,
which the real backend meets only with the buffer empty in the range; `store.restore`'s proof then
needs that premise of its backend at restore time.

**Possible fixes**: document the precondition on `UnsafeReader.UnsafeRange`; or, for a positive
limit, read `limit` entries from both and merge them (the buffer's entries replace bbolt's at the
same key), then cut to `limit`.

**Found**: 2026-10-23, planning `store.restore`'s proof (the restore plan's R4b), reading the
backend bridge's range lemma (`rtRange_safe`, `BackendBridge.lean`), which holds for limit `0`.
