---
upstream: unchecked
checked: 2026-10-23
links: []
---

# A limited `ReadTx.UnsafeRange` skips committed entries when the read buffer has some in range

**Status**: an unstated precondition (API documentation). With a positive limit, the read
transaction's range read is a prefix of the range only when its read buffer holds no entry of
the range. etcd's one caller that pages through a bucket with it, `store.restore`, meets that
(the buffer has no `Key` entry when it runs), as far as checked; nothing documents it, so a new
caller, or a change that writes to the `Key` bucket before `restore`, would skip entries silently.

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
them. (The model: `rtRange` in `Proof/go_etcd_io/etcd/server/v3/storage/backend/Model2.lean`.)
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
