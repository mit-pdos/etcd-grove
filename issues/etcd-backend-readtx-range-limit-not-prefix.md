---
upstream: unchecked
checked: 2026-10-16
links:
  - etcd-io/etcd#22594 pr open: passes a limit to this range (syncWatchers' bounded scan) and gets the non-prefix result
---

# A read transaction's limited range of the `key` bucket is not a prefix of the range

**Status**: an unstated property of the backend API (no bug in the pinned code's callers, as far
as checked). `ReadTx.UnsafeRange(bucket, key, endKey, limit)` with `limit > 0` that cuts the
range does not return the first `limit` entries of `[key, endKey)`: with `n` entries of the range
in the read buffer (the writes not yet committed, which have the highest keys of a safe-range
bucket such as `key`), it returns, if `n < limit`, bbolt's first `limit - n` entries followed by
all `n` of the buffer's, skipping the entries between, and if `n ≥ limit`, the buffer's first
`limit` entries and none of bbolt's. `UnsafeReader.UnsafeRange` has no documentation saying what the limit means.

**Where**: `server/storage/backend/read_tx.go:78-121` (`baseReadTx.UnsafeRange`: the read
buffer's range first, `if int64(len(keys)) == limit { return }`, then
`unsafeRange(c, key, endKey, limit-len(keys))` and `append(k2, keys...)`), at the pinned etcd
revision of `etc/goose.py`. The Lean model of it is `backend.rtRange`
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/Model2.lean`), proved of the code
(`Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__UnsafeRange.lean`).

**What happens**: with 20 committed revisions (2..21) and 5 buffered (22..26) of a key,
`rangeEvents(lg, b, 2, 27, 10, c)` of etcd-io/etcd#22594 (which passes its limit through to
this range) returns revisions `[2 3 4 5 6 22 23 24 25 26]`, not `[2 .. 11]`:
`notes/pr-verify/etcd-22594/watchable_store_rangeevents_limit_test.go` (against the PR's head).

The pinned code's callers with a limit on a safe-range bucket through a `ReadTx`: the store's
`restore` (`server/storage/mvcc/kvstore.go`, chunks of `restoreChunkKeys`), which reads with
the read buffer empty (`NewStore` force-commits before it; `Restore` is of a fresh backend),
so it gets prefixes. The compaction's limited ranges are of the batch transaction (bbolt's
transaction, no read buffer).

**Expected**: either the documented behavior "at most `limit` entries, the first ones in key
order", or documentation that a limit is only meaningful when the range has no buffered entries.

**How the proof handles it**: mvcc's contract of the backend's range read
(`keyRangeReadSpec`, `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean`) promises the
range only for a limit that does not cut it (`lim ≤ 0` or at least the range's length): on
branch `pr-verify/etcd-22594`, where the limit was added; on `lean` the contract has limit `0`
only.

**Possible fixes**: in `baseReadTx.UnsafeRange`, for a range with a limit, read bbolt's part
first with the whole limit, then the buffer's with what is left (a safe-range bucket's buffer
keys are above bbolt's); or document the limit's meaning.

**Found**: 2026-10-16, verifying etcd-io/etcd#22594 (`etcd-pr-verify`): the PR's `rangeEvents`
spec needs the limited range, which the backend's proved model shows is not a prefix.
