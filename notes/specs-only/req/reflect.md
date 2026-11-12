# Requirements on `reflect` (Perennial's; names-only)

## from 4d

`reflect.DeepEqual(a, b)` on two `map[common.Pgid]struct{}` (`hashMap.mergeSpans`'s `Verify`
check, `internal/freelist/hashmap.go:179,182`: panics unless the three span maps agree): returns
whether they have the same keys. The old local trust-boundary spec
(`specs-ref/Spec/reflect/DeepEqual.lean`, `spec_pgidSet`) is enough. Used by: the hash map's
realization of `flOwn` (`Interface.ReleasePendingPages.spec`, through `mergeSpans`).
