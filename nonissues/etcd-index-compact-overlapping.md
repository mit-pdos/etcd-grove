---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---

# mvcc: two overlapping treeIndex.Compact passes can panic or delete a re-put key

`treeIndex.Compact` clones the tree, then compacts each key index under the lock and deletes emptied
ones by key. Two overlapping passes can compact a key index the other already emptied (`lg.Panic("'compact'
got an unexpected empty keyIndex")`), or delete a newer key index of a key put again in between.

**Why not an issue:** a precondition etcd meets: the only caller is the store's compaction job,
which the store's FIFO scheduler runs one at a time, at increasing revisions. At most a missing doc
comment on the unexported `index` interface (none at upstream `main` 3aaab3479, 2026-10-23).

## Proof

no: `treeIndex.Compact`'s spec takes the compactor's exclusive token
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/treeIndex__Compact.lean`), which the store passes from
job to job.

## Notes

Reproduced 2026-10-13 by a test in `server/storage/mvcc` running pass B's loop body by hand after
pass A (not kept): `PANIC 'compact' got an unexpected empty keyIndex {"key": "k"}`.
