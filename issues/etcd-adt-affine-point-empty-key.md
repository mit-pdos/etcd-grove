---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#22358 pr open: fixes the same class (a point interval whose End is not above its Begin) for int64 only
---

# `NewStringAffinePoint("")` and `NewBytesAffinePoint(nil)` have End < Begin

- **Status**: a wrong result in an exported API of `go.etcd.io/etcd/pkg/v3/adt`, unreachable from
  etcd's own callers (they reject empty keys first).
- **Where**: `pkg/adt/interval_tree.go` at the pinned revision (`upamanyus/etcd` `09669450f`):
  `NewStringAffinePoint` (line 892: `[s, s + "\x00")`), `NewBytesAffinePoint` (945: `[b, b ++
  [0])`). In the affine order the empty string/slice is the top element (`+inf`), so for the empty
  key the point is `["", "\x00")`, with `Begin` above `End`.
- **What happens**: `Begin.Compare(End)` is `1`; `Stab(NewStringAffinePoint(""))` on a tree holding
  `[a, +inf)` (`NewStringAffineInterval("a", "")`) returns nothing. Reproduction:
  `notes/pr-verify/etcd-22358/review_probe_test.go` on branch `pr-verify/etcd-22358`
  (`TestReviewProbe`, the last two lines of `review-probe-head.log` there).
- **Expected**: a point interval with `Begin <= End` (or documentation that the empty key has no
  point interval, as `+inf` has no successor: the int64 analogue of etcd#22358's `MaxInt64` case).
- **How the proof handles it**: `Spec/go_etcd_io/etcd/pkg/v3/adt/NewStringAffinePoint.lean` and
  `NewBytesAffinePoint.lean` state the returned value exactly and claim no order between its ends;
  etcd's callers never pass an empty key: `v3rpc` rejects empty keys before `checkIntervals`
  (`server/etcdserver/api/v3rpc/key.go`, `checkTxnRequest` before `checkIntervals`), the auth
  store's `isValidPermissionRange` rejects an empty key (`server/auth/range_perm_cache.go:190`),
  and watch event keys are never empty.
- **Possible fixes**: document the restriction (non-empty key), or return an empty interval for
  the empty key as etcd#22358 does at `MaxInt64`.
- **Found**: 2026-10-17, by the reviewer of the verification of etcd#22358 (the same class as the
  PR's `NewInt64Point(MaxInt64)` fix).
