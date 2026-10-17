# Files of the verification of etcd-io/etcd#22495

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `wait-tests-fork.log` | The PR's `pkg/wait` tests (`TestWaitTimePending`, `TestWaitTimeTriggerReleasesOnlyEarlierDeadlines`, the old ones) pass on the verified code. | `mit-pdos/etcd-grove` branch `pr-etcd-22495-goose-lean` (`fe380dea3`) | `cd pkg && GOTOOLCHAIN=go1.27.1 go test ./wait/ -count=1 -v -run 'WaitTime\|Trigger'` |
| `wait_time_model_test.go` | A randomized check of `timeList` against a reference model (random `Wait`/`Trigger`, including triggers below the last one and repeated deadlines): every channel is closed exactly when the model releases it, `Pending()` is the number of distinct deadlines waiting. Not a finding: it supports the verdict alongside the proof. | the PR head `6f89dd529` (etcd-io/etcd) | `cp wait_time_model_test.go <checkout>/pkg/wait/ && cd <checkout>/pkg && go test ./wait/ -run TestWaitTimeModel -v` |
| `wait_time_model_test-pr-head.log` | Its output on the PR head: passes. | PR head `6f89dd529` | as above |

The server's `go test ./etcdserver/` (in `server/`) also passes on the fork branch (`ok go.etcd.io/etcd/server/v3/etcdserver 8.153s`).
| `wait_time_review_test.go` | The reviewer subagent's randomized model test (`TestReviewModel`, 2000 seeds × 300 steps, decreasing triggers, repeated waits, `Pending` and heap/map sizes) and a concurrent `-race` stress test (`TestReviewConcurrent`, 8 goroutines). | PR head `6f89dd529` | `cp wait_time_review_test.go <checkout>/pkg/wait/ && cd <checkout>/pkg && go test -race ./wait/ -run TestReview -v` |
| `wait_time_review_test-pr-head.log` | Its output on the PR head: passes. | PR head `6f89dd529` | as above |
