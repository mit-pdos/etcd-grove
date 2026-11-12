# Requirements on `go.etcd.io/bbolt/internal/freelist` (batch 4d)

## from 4c

bbolt's public API (`SpecPlan/Spec/go_etcd_io/bbolt/`, namespace `Bbolt`) keeps the freelist in its
invariants: `flOwn db.freelist F` under `rwlock` (the writer's), `flReaders db.freelist R` under
`metalock` (`R` the txids of the registered read transactions). Its sketches rely on:

1. **Readers registered at begin, removed at rollback** (`DB.Begin.spec` read, `Tx.Rollback.spec`):
   `AddReadonlyTXID(tx.meta.Txid())` / `RemoveReadonlyTXID` under `metalock`, concurrent with the
   writer's `Allocate`/`Free` (which touch only `flOwn`'s fields).
2. **The writer releases what no reader sees** (`DB.Begin.spec` write): `ReleasePendingPages()`
   with the readers `R`: every released page is `releasable` (no reader `r` with `alloc ≤ r <
   freer`), which is the reason a page a live read transaction reaches is never reused (the
   snapshot isolation `boltTx`'s view relies on).
3. **Allocation and freeing in a commit** (`Bucket.spill.spec`, `Tx.commitFreelist.spec`,
   `Bucket.DeleteBucket.spec`): `Allocate(txid, n)` returns a run of free pages (or `0`: none, then
   bbolt grows past the high-water mark), `Free(txid, p)` of a page and its overflow makes it pending
   for `txid` (its premise `canFree`: bbolt frees each extent of the old tree once, from its
   well-formed file: extents disjoint, none already free); `Rollback(txid)` undoes both
   (`Tx.Rollback.spec`, a failed `Commit`).
4. **The freelist page** (`Tx.commitFreelist.spec`, `Open.spec`'s `loadFreelist`):
   `EstimatedWritePageSize` bounds what `Write` writes (`ReqEstimate`), `Write` then `Read` (or
   `Reload` after a failed commit) gives back the free pages and the pending ones as free; under
   `NoFreelistSync` (etcd), `NoSyncReload(freepages)` / `Init` from the ids the tree does not reach
   (`DB.freepages`, run on the spare reader slot).
5. **Counts for the statistics** (`Tx.close` before `DB.Stats.spec`): `FreeCount`, `PendingCount`,
   `EstimatedWritePageSize` with any result (no precondition but `flOwn`).
6. **The id bound** `flMaxIds = 2^59`: bbolt meets it from the high-water mark (`hwm ≤ 2^36` pages
   of 4096 bytes in a mapping of at most `2^48` bytes), as 4d's header says.

## from 4d (round 1: what 4c must keep)

`Interface.Init`, `Read`, `Reload` and `NoSyncReload` take the premise **"the new free pages are
not empty, or no page is free"** (`F.free = GMap.empty`): the hash map's `Init` with no ids returns
before rebuilding its cache (`nonissues/bbolt-hashmap-init-empty-stale-cache.md`). For
`NoSyncReload(ids)` it is `ids.filter (· ∉ F.pending) ≠ [] ∨ F.free = ∅`; for `Read`/`Reload(p)`,
`freelistIdsOf bs ≠ [] ∨ F.free = ∅`. 4c meets it with the invariant **"the in-memory free pages
are among the last commit's freelist ids (a synced freelist) or the pages no committed tree reaches
(`freepages`)"**: a free page is never in a committed tree, so it is in the reload's ids; ids that
are empty (or all pending) then mean no page is free. `loadFreelist` meets it trivially (a new
freelist). The freelist's constructors now return `arrayIface l` / `hashMapIface l`
(`flOwn_dyn`); the interface specs are unchanged in shape (`Interface.<M>.spec`). Also: `Reload`
no longer takes `F.count < flMaxIds`; `freelistPage_read` (common) takes `Write`'s own room
(`estimatedSize`), so `Write`'s post composes with it directly; `DefaultPageSize` is 4096
(`BboltCommon.init.spec`); `BboltCommon.meta_in_sector` is your item 1's `16 + 64 ≤ 512`.
