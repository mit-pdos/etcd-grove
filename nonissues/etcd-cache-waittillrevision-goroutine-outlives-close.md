---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# cache: a consistent `Get`'s timeout goroutine outlives `Close`

[`waitTillRevision`](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/cache/cache.go#L240-L275),
called by every linearizable `Get` whose revision the cache has not reached, starts a goroutine that
waits for `time.After(WaitTimeout)` or the caller's context and then broadcasts on the store's
condition variable. The goroutine is not counted in the cache's wait group and does not watch the
cache's own context, so it keeps running (up to `WaitTimeout`, 3s by default, after the `Get`
returned) after `Close` returned, contrary to `Close`'s comment ("blocks until all goroutines
return"); a burst of such `Get`s leaves one goroutine each.

**Why not an issue:** no test; found by code reading (batch 1g of the specs-only branch). The
goroutine touches only the store's condition variable, so nothing goes wrong after `Close`:
resource use and a documentation mismatch, no wrong result. A test could promote it with
`goleak` after `Close` following a waiting `Get`.

## Proof

no: the specs-only branch's `Cache.waitTillRevision.spec` gives the caller nothing tied to the
goroutine, and `Close.spec` does not claim every goroutine has stopped.

## Notes

Fix, if wanted: select on `c.internalCtx.Done()` and the `Get`'s own return (a `done` channel
closed by a `defer`), or count the goroutine in the wait group.
