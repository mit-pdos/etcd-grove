---
upstream: none
checked: 2026-11-06
links:
blocks-proof: no
---

# bbolt: a database reopened without a sync reuses pages freed by a commit whose meta page is only in the page cache

A process killed between a commit's meta-page write and its `fdatasync`, and restarted while the
machine stays up, opens the database at that meta page, read from the page cache, with the pages
that commit freed on its freelist. Its first write transaction overwrites them, but they still
belong to the previous, durable meta page's tree. A power loss during that transaction's
`fdatasync` can persist the overwrites without the newer meta page: the next `Open` uses the older
meta page, whose checksum is valid and whose tree now has overwritten pages, a corrupt database
(a panic or wrong data in etcd).

**Why not an issue:** no test, found by code reading (`notes/restart-vs-crash.md`, "bbolt"); it
needs a process restart without a sync, a write transaction within the writeback window, and a
power loss during that transaction's `fdatasync`, which bbolt's and etcd's documentation do not
exclude but no test harness here reaches.

## Execution

At bbolt v1.5.0 (the release etcd's `go.mod` pins; the goosed fork, upamanyus/bbolt@3207bac, has
the same code at shifted lines: `writeMeta` `tx.go:604-634`, `meta()` `db.go:1182`).

1. G1 commits transaction *n* (`Tx.Commit`, `tx.go:170-283`): it frees the pages tree *n−1* no
   longer uses (pending on tx *n*: the nodes it rewrote, and the old freelist page, `tx.go:216`),
   writes its dirty pages and the freelist and `fdatasync`s (`Tx.write`, `tx.go:520-592`, `:568`),
   then writes meta page *n* (`writeMeta`, `tx.go:595-623`, `writeAt` at `:606`) and is killed
   before that `fdatasync` (`:615`). Tx *n*'s pages are durable; meta *n* is a dirty page of the file.
2. G2 opens the database on the page cache: `Open` (`db.go:178`) reads both meta pages through the
   mmap and uses the valid one with the higher txid (`meta()`, `db.go:1141-1162`), meta *n*; the
   freelist is read from meta *n*'s freelist page (`loadFreelist`, `db.go:422-436`), which holds
   the free and the pending ids (`Copyall`, `internal/freelist/shared.go:205-213`, `:302`, `:308`),
   so the pages tx *n* freed, which belong to tree *n−1* only, are free to G2 (with no synced
   freelist, `freepages` rebuilds it from tree *n*, the same set).
3. G2's first write transaction (etcd's backend commits at boot and every 100 ms) allocates those
   pages and overwrites them. Its writes and meta *n* are dirty pages of the one file.
4. Power loss before the cache flush that ends G2's first `fdatasync`: pages reach the device in
   any order before the flush, so the overwrites can be durable and meta *n* not.
5. G3 opens at meta *n−1*, valid, whose tree points at overwritten pages.

Under machine crashes alone it cannot happen: if meta *n* is not on disk, the next `Open` uses
meta *n−1*, whose freelist does not contain tree *n−1*'s pages.

## Proof

no: the Linux file extension assumes a restart follows a machine restart or a `sync(2)` of what
the old process left (`GooseLang/Ext/Fs/Impl.lean`, header "Restarts"), so a process restart is a
machine crash and every generation boots on a durable state; this execution is outside the
theorem, by that stated assumption.

## Fix

The note's proposal (`notes/restart-vs-crash.md`, conclusion 4): `db.Sync()` (an `fdatasync`,
`db.go:1095`) at the end of `Open` in read-write mode, before the first write transaction; it
writes meta *n* with G1's other dirty pages, so a later transaction reuses only pages no durable
meta needs. (Or etcd's backend calls `db.Sync()` right after `bolt.Open`,
`server/storage/backend/backend.go:233`.)
