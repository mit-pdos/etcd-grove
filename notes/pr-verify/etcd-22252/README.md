# etcd-io/etcd#22252: tests, probes and logs

Revisions: PR head `cd4a82b516cf129c6bd16a28df09e09e3627a83e`; its upstream base (merge-base with
`main`) `7d7f884852f728972bf1e20c3f26840b6bbeb94c`; the verified fork branch `mit-pdos/etcd-grove`
branch `pr-etcd-22252-goose-lean` (`853cc10e8`, the PR's non-test diff onto `goose-lean`
`09669450f`, applied cleanly). Run from a checkout of the revision, with `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `pr-tests-base.log` | the PR's `TestInt64ComparableCompare` (5 of 10 cases) and `TestIntervalCompareInt64Overflow` failing on the base | base with the PR's `pkg/adt/interval_tree_test.go` | `git show cd4a82b51:pkg/adt/interval_tree_test.go > pkg/adt/interval_tree_test.go; cd pkg && go test -run 'TestInt64ComparableCompare\|TestIntervalCompareInt64Overflow' ./adt` |
| `int64_extremes_probe_test.go` | etcd#22358's probe (copied from `pr-verify/etcd-22358`): `Stab` with endpoints near both ends of int64 against brute force; `Stab`/`Intersects` of `NewInt64Point(MaxInt64)` find nothing | PR head (passes; fails on the base, see `pr-verify/etcd-22358`) | `cp int64_extremes_probe_test.go <checkout>/pkg/adt/ && cd <checkout>/pkg && go test -count=1 -run TestProbeInt64Extremes -v ./adt` |
| `probe-head.log` | its output on the PR head: both pass | PR head | as above |
| `int64_maxpoint_probe_test.go` | the reviewer's randomized probe: trees containing the unfixed `NewInt64Point(MaxInt64)` = `[MaxInt64, MinInt64)`, checking order, `max` fields, red-black properties, Insert/Delete/Find/Stab/Visit/Intersects/Contains/Union against brute force, with this PR's constructor and with etcd#22358's | PR head (passes) | `cp int64_maxpoint_probe_test.go <checkout>/pkg/adt/ && cd <checkout>/pkg && go test -count=1 -v ./adt` |
| `probe-output.txt` | its output (the full `pkg/adt` suite with the probe) | PR head | as above |
