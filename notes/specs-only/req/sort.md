# Requirements on `sort` (Perennial's)

## from 4d

1. `sort.Sort(x)` on a `common.Pgids` (`freelist.Read`, `mergeSpans`, `Copyall`, the hash map's
   `freePageIds`) and on `freelist.txIDx` (`ReleasePendingPages`): Perennial's spec, through the
   types' `Len`/`Less`/`Swap` (`BboltCommon.Pgids.Len/Less/Swap.spec`; `txIDx`'s are internal).
   Its `2^62` size bound is a premise of the freelist specs that sort (`flMaxIds`,
   `R.length < 2^62`).
2. `sort.Search(n, f)` (`Mergepgids`, `internal/common/page.go:394`): Perennial's spec.
3. `sort.SliceIsSorted(x, less)` (`hashMap.Init`, `internal/freelist/hashmap.go:30`: panics unless
   sorted): names-only in Perennial; the old local trust-boundary spec
   (`specs-ref/Spec/sort/SliceIsSorted.lean`: on a slice, with a `less` answering `<` on its
   indices, returns whether no `less(i, i-1)`) is enough. Used by: `Interface.Init.spec` (and
   `Read`, `Reload`, `NoSyncReload` through it), the hash map's realization of `flOwn`.
