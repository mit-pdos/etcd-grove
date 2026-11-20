---
upstream: none
checked: 2026-11-18
links:
  - kubernetes/kubernetes#141652 issue open: the tracking issue of the model-based correctness tests (watch validation)
blocks-proof: no
---

# k8s correctness.WatchValidator's revision range wraps for a watch requested at resource version 2^64 - 1

`watchRevisionRange` (`apiserver/pkg/storage/testing/correctness/watch.go`) raises the start of a
watch's event range to `requestedRV + 1` (for `Exact`, for the legacy match, and for
`NotOlderThan` through `max`) in `uint64`. A request whose resource version parses to
`math.MaxUint64` ("18446744073709551615") wraps that start to 0, so `validateReliable` compares the
watch's events against every change from revision 0 on (for `NotOlderThan`, `max` keeps the events'
own start instead of an empty range).

**Why not an issue:** found by code reading (k8s 7g, B5), at master of 2026-10-21
(`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`); unreachable in `TestCorrectness`'s use.
Its traffic draws watch resource versions from the store's (etcd revisions, `int64`, so below
`2^63`) plus small offsets, never `2^64 - 1`; our driver's `genWatchFrom`/`minRV` clamp every drawn
resource version below `2^62 + 201`. A real API server never sees such a watch succeed either: etcd
rejects a revision above its own.

## Proof

no: B5 (`validateWatchL_of_watchOkL`, `Proof/.../k8s/etcd3/RealWatch.lean`) takes the premise
`hreq` (the requested resource version parses below `2^63`), discharged in step 5 from `InOk`;
without it B5 is false (the checker's range starts at 0 where the driver's natural-number range is
empty).

## Notes

Fix, if wanted: reject (or saturate at) `requestedRV == math.MaxUint64` before adding one.
