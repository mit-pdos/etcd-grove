---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# cache: `Cache.Watch` concurrent with `Cache.Close` can panic in `sync.WaitGroup`, or outlive `Close`

[`Close`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/cache/cache.go#L306-L310)
cancels the cache's context and waits on its wait group, whose counter falls to zero as the resync
loop, the watch loop and the watchers' goroutines return. A
[`Watch`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/cache/cache.go#L116-L190)
that passed `WaitReady` still runs `c.waitGroup.Add(1)` (L142): at the counter's zero with a
waiter, `Add` panics ("WaitGroup misuse: Add called concurrently with Wait"); just after, the waiter
panics ("WaitGroup is reused before previous Wait has returned"); after `Wait` returned, `Close` has
returned while the new watcher's goroutine runs, contrary to its comment ("blocks until all
goroutines return"). Neither method documents that they must not overlap.

**Why not an issue:** no test; found by code reading (bounds plan B3's wait-group inventory,
`notes/bounds-waitgroups.md`), and an undocumented precondition etcd's users meet: the package's
only caller in etcd is its integration test (`tests/integration/cache_test.go`), which does not
overlap them. A test could promote it: `Watch` calls in a loop on a ready cache while `Close` runs,
until a panic (racy, but the `Add` window is a few instructions wide each time the counter reaches
zero).

## Proof

no: the proof takes the precondition as the "open" token `cacheOpen`
(`Proof/go_etcd_io/etcd/cache/v3/InvCache.lean`, `cacheWgInv`): `Watch` holds a fraction, `Close`
needs the whole, so a verified caller never overlaps them.

## Notes

Fix, if wanted: a mutex-guarded `closed` flag set by `Close` before `Wait` and checked by `Watch`
around its `Add(1)` (returning a closed channel after `Close`), or documentation.
`notes/decisions.md`'s entry on the cache's wait group first called the token conservatism; that
was wrong (corrected there, 2026-11-01). The same shape in the leasing KV:
`nonissues/etcd-leasing-get-during-close-waitgroup.md`.
