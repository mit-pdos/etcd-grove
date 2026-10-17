---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22357 issue open: reports the Compare wrap (MaxInt64 vs MinInt64 compares as -1)
  - etcd-io/etcd#22358 pr open: fixes Compare (direct comparison) and NewInt64Point at MaxInt64 (empty [a, a)); verified on branch pr-verify/etcd-22358
  - etcd-io/etcd#22252 pr open: fixes the same Compare overflow
---

# `Int64Comparable.Compare` wraps for far-apart values; `NewInt64Point(MaxInt64)` has End < Begin

- **Status**: a bug (wrong result) in an exported API of `go.etcd.io/etcd/pkg/v3/adt`. No
  production code in etcd uses the int64 intervals (only tests and `example_test.go`); the
  in-tree users of the interval tree use string- or bytes-affine intervals.
- **Where**: `pkg/adt/interval_tree.go` at the pinned revision (`upamanyus/etcd` `09669450f`,
  the same code as upstream `main` before etcd#22358): `Int64Comparable.Compare` (lines
  910–920: `cmp := v - vc`, the sign of a wrapping difference), `NewInt64Point` (904–906:
  `Int64Comparable(a + 1)`).
- **What happens**: `Int64Comparable(math.MaxInt64).Compare(Int64Comparable(math.MinInt64))`
  is `-1`, and `MaxInt64` vs `-1` is `-1`; any two values more than `2^63 - 1` apart compare
  in the wrong order, so an interval tree over int64 intervals with such endpoints is
  mis-ordered and `Stab`/`Intersects` miss intervals. `NewInt64Point(math.MaxInt64)` is
  `[MaxInt64, MinInt64)`. Reproduction: `notes/pr-verify/etcd-22358/int64_extremes_probe_test.go`
  on branch `pr-verify/etcd-22358` (`TestProbeInt64ExtremesRandom` fails on the base:
  intervals `[MinInt64+1, 1)`, `[MinInt64+1, 2^62)`, `[-2^62, 2)`, `Stab(1)` finds 0 of 2), and
  etcd#22358's `TestInt64ComparableCompareExtremes` (`expected: 1, actual: -1`).
- **Expected**: the signed order of int64, as the other comparators of the package give their
  orders; a point interval with `Begin <= End`.
- **How the proof handles it**: on `lean`, neither function is specified (translated only, no
  linked result uses them). Branch `pr-verify/etcd-22358` specifies and proves both as fixed by
  etcd#22358 (`Spec/go_etcd_io/etcd/pkg/v3/adt/Int64Comparable__Compare.lean`,
  `NewInt64Point.lean`) and models the old code's results
  (`Proof/go_etcd_io/etcd/pkg/v3/adt/Int64Ivl.lean`, `int64CmpOld_wrong`, `int64PointOld_wrong`).
- **Possible fixes**: compare `v < vc` / `v > vc` directly (etcd#22358, etcd#22252); special-case
  `NewInt64Point(math.MaxInt64)` (etcd#22358: the empty `[a, a)`, which overlaps no interval since
  no half-open int64 interval contains `MaxInt64`).
- **Found**: 2026-10-17, by the verification of etcd#22358 (already reported upstream as #22357).
