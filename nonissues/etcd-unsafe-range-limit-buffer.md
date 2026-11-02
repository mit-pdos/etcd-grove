---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#22594 pr open: passes a positive limit to `rangeEvents`' `ReadTx.UnsafeRange` on the `Key` bucket (`syncWatchers`), over the newest revisions, which the read buffer holds: merged as is, this precondition breaks there (skipped events); its review does not mention it
  - etcd-io/etcd#22264 issue open: what #22594 addresses (the unbounded `syncWatchers` scan); related, different
  - etcd-io/etcd#21986 issue open: the read buffer's merge skips deduplication; same code, different bug
  - etcd-io/etcd#22298 pr open: deduplicates the write buffer on every path into the read buffer (#21986); same code, different bug
  - etcd-io/etcd#21987 pr open: deduplicates in writeback before the merge (#21986); related, different
  - etcd-io/etcd#15961 pr closed: `UnsafeRange` with limit 1 when `endKey` is nil; same function, different issue
blocks-proof: no
---

# backend: a limited ReadTx.UnsafeRange skips committed entries when the read buffer has some in range

With a positive limit, `ReadTx.UnsafeRange` takes up to `limit` entries from the read buffer, then
`limit - n` from bbolt, and returns bbolt's followed by the buffer's: when bbolt has more than
`limit - n` entries in range, the ones between are not returned, so a caller paging on from the last
key returned skips them.

**Why not an issue:** no test (code reading), and a precondition etcd's one paging caller meets:
`store.restore` pages the `Key` bucket when its read buffer has no entry there (`NewStore`
force-commits first, `Restore` runs on a freshly opened backend, and `restore` holds the read lock
across the loop); compaction's limited range goes through the batch transaction, which reads bbolt
alone. Undocumented on `UnsafeReader.UnsafeRange`.

## Proof

no: `store.restore`'s proof is to take the premise of an empty read buffer at restore time, which
`NewStore` and `Restore` meet (`notes/restore-plan.md`, R4b).

## Notes

etcd-io/etcd#22594, if merged as is, would be a caller that breaks it: `syncWatchers` would page the
newest revisions with a limit through the buffered `ReadTx`, and an unsynced watcher could miss
events. Worth a review comment there, with a test, before it merges; a fix merges the buffer's and
bbolt's entries before cutting to `limit`.
