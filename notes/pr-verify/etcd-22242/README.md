# Files of the verification of etcd-io/etcd#22242

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `read_logsink_test.go` | Two unit tests of the read loop with a log sink that blocks in `Write` (a stalled log file). `TestReadLoopStalledSink_SlowIteration`: an iteration slower than 100 ms logs its trace, and the next linearizable read must still complete (#22214's goroutine dump). `TestReadLoopStalledSink_ReadIndexRetry`: a ReadIndex response later than `readIndexRetryTime` (set to 50 ms) makes `requestCurrentIndex` log its retry warning on the loop's goroutine, and the read must still complete. | upstream base `a279d15ac`; PR head `3d53e5a41`; `mit-pdos/etcd-grove` branch `pr-etcd-22242-goose-lean` (`f2fbb4964`) | `cp read_logsink_test.go <checkout>/server/etcdserver/read/ && cd <checkout>/server/etcdserver/read && GOTOOLCHAIN=go1.27.1 go test -count=1 -run StalledSink -v .` |
| `read_logsink_test-upstream-base.log` | At the base both fail: the slow iteration's trace parks the loop (the next read's ReadIndex is never sent, `read_logsink_test.go:60`), and the retry warning parks it (`:71`, "hung"). | upstream `a279d15ac` | as above |
| `read_logsink_test-pr-head.log` | With the PR the first passes (the PR's fix) and the second still fails: the loop parks in `requestCurrentIndex`'s `lg.Warn`. | PR head `3d53e5a41` | as above |
| `read_logsink_test-fork-branch.log` | The same on the verified fork branch (the PR applied onto the pin). | `pr-etcd-22242-goose-lean` `f2fbb4964` | as above |
| `read_review_test.go` | The reviewer's probe (`TestReviewSlowSink`): a sink taking 400 ms per write and four read-loop iterations of about 120 ms; prints the dropped-trace counter and each logged trace's `duration` and when it was written. Shows the logged `duration` includes the time a trace waited (0.40 s logged for a 0.12 s iteration) and that the logger goroutine writes after the loop has returned (437 ms later). Uses `droppedReadLoopTraces`, so PR head only. | PR head `3d53e5a41` | `cp read_review_test.go <checkout>/server/etcdserver/read/ && cd <checkout>/server/etcdserver/read && GOTOOLCHAIN=go1.27.1 go test -race -count=1 -run TestReviewSlowSink -v .` |
| `read_review_test-pr-head.log` | Its output (passes; `-race` clean). | PR head `3d53e5a41` | as above |

The PR's own test, `TestLinearizableReadLoop_BlockedLogSink` (in its `read_test.go`), passes at its
head and on the fork branch (`go test -race -count=3 -run BlockedLogSink .`).
