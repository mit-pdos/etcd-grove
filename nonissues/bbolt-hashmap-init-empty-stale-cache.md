---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# bbolt: the hashmap freelist's Init with no ids keeps the old free-page cache

`hashMap.Init(pgids)` with an empty `pgids` clears the free spans and returns before `reindex`, so
the freelist's cache of free and pending page ids keeps the ids that were free before. Those pages
are then neither free nor allocatable, yet `Freed` reports them freed, and a later `Free` of one of
them panics with "page N already freed".

**Why not an issue:** a precondition bbolt meets, found by code reading: the freelist package is
internal, and bbolt reaches an empty `Init` on a non-empty freelist only through `Reload` or
`NoSyncReload` after a failed commit, whose ids include every id that was free (the synced
freelist page holds the free and pending ids of the last commit; `freepages()` returns every page
unreachable from the committed tree). `Open` initializes a fresh freelist, whose cache is empty.

## Proof

no: the freelist's `Init`, `Read`, `Reload` and `NoSyncReload` specs take the premise that the new
free pages are not empty or no page was free (`Spec/go_etcd_io/bbolt/internal/freelist/Interface__{Init,Read,Reload,NoSyncReload}.lean`,
the `Interface.<M>.contract`s, and the `array`/`hashMap` instances), which the commit's rollback
paths meet as above (bbolt's invariant: the in-memory free pages are among the last commit's
freelist ids or the pages no committed tree reaches; `req/go_etcd_io_bbolt_internal_freelist.md`)
and `loadFreelist` meets trivially (a new freelist).

## Notes

At etcd-io/bbolt@e7a8b2dd498494a3766ba24dd94d3509e5588485 (v1.5.0, etcd's):
[`hashMap.Init`](https://github.com/etcd-io/bbolt/blob/e7a8b2dd498494a3766ba24dd94d3509e5588485/internal/freelist/hashmap.go#L23-L59)
returns at `len(pgids) == 0` (line 30) before `f.reindex()` (line 58), which rebuilds
[`shared.cache`](https://github.com/etcd-io/bbolt/blob/e7a8b2dd498494a3766ba24dd94d3509e5588485/internal/freelist/shared.go#L243);
`shared.Free` panics on a cached id (line 80). The array freelist's `Init` has no early return.
Found by the old bbolt proof (`old/bbolt/notes/STATUS-bbolt.md`) and again by U2 of the current
one.
