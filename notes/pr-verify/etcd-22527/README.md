# etcd-io/etcd#22527: tests and logs

The tests the report (`notes/pr-verify/etcd-22527.md`) relies on. Each `.go` file is a test file of
package `etcdserver` (`server/etcdserver/` in etcd). It builds a server the way the PR's
`TestPublishV3WaitsForApplyAfterTooManyRequests` does. Run a file in a checkout of the revision
named below:

```
cp <file> <checkout>/server/etcdserver/
cd <checkout>/server && GOTOOLCHAIN=go1.27.1 go test -count=1 -v -run '<Names>' ./etcdserver/
```

Revisions:

- PR head: `6d1df10c5`, upstream `pull/22527/head`.
- Upstream base: `91703b3d4`, `merge-base` of the PR and upstream `main`.
- Fork branch: `mit-pdos/etcd-grove` branch `pr-etcd-22527-goose-lean` (`f2d7cf431`). This is
  the fork's `goose-lean` `09669450f` with the PR applied, the code that was verified.

| File | What it shows | Revision |
|---|---|---|
| `server_publish_probe_test.go` | `TestPublishV3ProbeTimeoutRetries`: the apply never catches up and the publish timeout is 20 ms. Over 200 ms the PR head logs 10 rejections, one per timeout. The base logs 5632, the tight loop of #22526. `TestPublishV3ProbeStopDuringWait`: a stop during the wait ends `publishV3` without a proposal. `TestPublishV3ProbeApplyWaitAheadOfAppliedIndex`: `applyWait` is triggered past the wait's deadline while `s.appliedIndex` stays 0, the state #22516 leaves after a snapshot. The wait then ends at once, and the PR head still logs thousands of rejections in 100 ms. The test passes when there are at least 100 rejections. | PR head and base |
| `server_publish_reviewer_test.go` (the reviewer's) | `TestReviewerPublishV3SpinsAfterSnapshotTrigger`: the same snapshot case as above. It fails on purpose: "still retries in a tight loop". `TestReviewerPublishV3RejectedOncePerApplyBatch`: the committed index advances during the wait, staying 6000 past the applied index. Each wakeup's retry is then rejected again: 20 rejections over 200 apply batches. The retries are bounded by apply progress, so this is not a tight loop. It fails on purpose: "wait ended with the limit still exceeded". | PR head |
| `tests-pr-head.log` | Output of both files and of the PR's own test on the PR head. Counts vary between runs: 2519 and 22275 in two runs of the snapshot probe. | PR head |
| `tests-base.log` | Output of `server_publish_probe_test.go` on the base. | base |

The fork branch passes `go build ./...` and `go test ./etcdserver/` in `server/`, with the PR's
test included.
