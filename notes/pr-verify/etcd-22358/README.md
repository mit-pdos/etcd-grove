# etcd-io/etcd#22358: tests, probes and logs

Revisions: PR head `283ea1d3c8d0d797d4043d52244b3f5eb51caef1`; its upstream base (merge-base with
`main`) `774da656e20285fb0bd20c205494675dc5f3b997`; the verified fork branch `mit-pdos/etcd-grove`
branch `pr-etcd-22358-goose-lean` (`473edb1011ce1e764b0aec6bf8e87f304c8de43c`, the PR's non-test
diff onto `goose-lean` `09669450f`, applied cleanly). Run from a checkout of the revision, with
`GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `int64_extremes_probe_test.go` | `TestProbeInt64ExtremesRandom`: `Stab` over int64 intervals with endpoints near both ends of int64 against brute-force containment; `TestProbeInt64ExtremesTree`: `Stab`/`Intersects` of `NewInt64Point(MaxInt64)` find nothing | base (fails), PR head (passes) | `cp int64_extremes_probe_test.go <checkout>/pkg/adt/ && cd <checkout>/pkg && go test -count=1 -run TestProbeInt64Extremes ./adt` |
| `probe-base.log` | the random probe failing on the base: intervals `[MinInt64+1, 1)`, `[MinInt64+1, 2^62)`, `[-2^62, 2)`, `Stab(1)` finds 0 of 2 | base | as above |
| `probe-head.log` | both probes passing | PR head | as above |
| `pr-tests-base.log` | the PR's own `TestInt64ComparableCompareExtremes` failing on the base (`expected: 1, actual: -1`) | base with the PR's `interval_tree_test.go` diff applied | `git diff 774da656e 283ea1d3c -- pkg/adt/interval_tree_test.go \| git apply; cd pkg && go test -count=1 -run 'TestInt64ComparableCompareExtremes\|TestNewInt64PointExtremes' ./adt` |
| `review_probe_test.go` | the reviewer's probe (logs only, no assertions): the point at `MaxInt64` is found by `Find` but not by `Stab`/`Intersects`; empty intervals `[a, a)` below `MaxInt64` do overlap in this tree; `NewStringAffinePoint("")`/`NewBytesAffinePoint(nil)` have `Begin > End` (`issues/etcd-adt-affine-point-empty-key.md`) | PR head | `cp review_probe_test.go <checkout>/pkg/adt/ && cd <checkout>/pkg && go test -count=1 -run TestReviewProbe -v ./adt` |
| `review-probe-head.log` | its output | PR head | as above |
