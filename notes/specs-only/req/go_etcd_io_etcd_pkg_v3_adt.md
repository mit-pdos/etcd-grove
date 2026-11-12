# Requirements on `go.etcd.io/etcd/pkg/v3/adt` (3f: the interval tree)

## from 3d

The auth store's permission cache (`server/auth/range_perm_cache.go`) keeps, per user, two interval
trees over bytes-affine keys. What its specs (`getMergedPerms.spec`, `checkKeyPoint.spec`,
`checkKeyInterval.spec`, through `Auth.cacheEntry p a u`) need:

1. `NewIntervalTree()`, `NewBytesAffineInterval(b, e)` (`e = nil`: infinity), `NewBytesAffinePoint(b)`
   (a `make` of `len(b) + 1`: the callers' premise `len < 2 ^ 63 - 1`), `Insert(ivl, v)`: a tree of the
   inserted intervals (any duplicates).
2. `Intersects(point)`: whether some stored interval contains the point (bytes order: W0's `keyLe`,
   `keyLt`).
3. `Contains(ivl)` for a proper interval (`begin < end`, or `end` infinity): whether the union of the
   stored intervals covers it (contiguously, as `Contains`' loop checks); for an empty or inverted
   interval, any answer. Stored intervals with non-empty begins never cover the empty key.
4. Read-only use from any goroutine once built (the cache's trees are replaced, never mutated).
```go
readPerms.Insert(ivl, struct{}{})                    // range_perm_cache.go:58
return cachedPerms.readPerms.Contains(ivl)           // range_perm_cache.go:96
return cachedPerms.readPerms.Intersects(pt)          // range_perm_cache.go:110
```
