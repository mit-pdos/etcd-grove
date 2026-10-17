# Files for the verification of etcd-io/etcd#22476

The report is `notes/pr-verify/etcd-22476.md`. Revisions: the PR head is `30eeae729` (etcd-io/etcd),
its merge base with upstream `main` is `d6af8028d`; the verified code is `mit-pdos/etcd-grove` branch
`pr-etcd-22476-goose-lean` (`050ea5ecd`: the PR onto the etcd pin `09669450f`). Go: `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `monitor_interval_test.go` | `EtcdServer.monitorDowngrade` with a negative `DowngradeCheckTime` (accepted by the configuration) panics at the PR head (`time.NewTicker`: "non-positive interval"); at the base it runs until stopped | PR head `30eeae729` (fails), base `d6af8028d` (passes) | `cp monitor_interval_test.go <checkout>/server/etcdserver/ && (cd <checkout>/server && go test -count=1 -run TestMonitorDowngradeNegativeInterval ./etcdserver/)` |
| `userspace_monitor_test.go` | `TCPProxy.runMonitor` with a negative `MonitorInterval` (`etcd gateway start --retry-delay=-1s`) panics at the PR head; at the base it runs until stopped | PR head (fails), base (passes) | `cp userspace_monitor_test.go <checkout>/server/proxy/tcpproxy/ && (cd <checkout>/server && go test -count=1 -run TestRunMonitorNegativeInterval ./proxy/tcpproxy/)` |
| `negative-interval.log` | the output of the two tests above at both revisions | | |
| `time_after_gc_test.go` | the PR's premise for its timer changes does not hold: 10^6 `time.After(time.Hour)` timers abandoned by a `select` leave the heap where it was (Go >= 1.23 collects unreferenced timers; the module's `go` directive is 1.27, and Go 1.27 removed `GODEBUG=asynctimerchan`) | base `d6af8028d` (passes; heap grew by -98304 bytes) | `cp time_after_gc_test.go <checkout>/server/storage/mvcc/ && (cd <checkout>/server && go test -count=1 -v -run TestTimeAfterInSelectIsCollected ./storage/mvcc/)` |
| `timer_stop_probe/` (`output.txt`) | `Stop()` on a fresh `time.NewTimer(0)` returns `true` (100000 of 100000, with and without a sleep in between), so the PR's drain `if !retryTimer.Stop() { <-retryTimer.C }` never runs; and after `Stop` no value arrives, so the drain, if it ran, would block forever | Go 1.27.1 | `cd timer_stop_probe && go run .` |
| `compaction-old-code.log` | the spec of `applierV3backend.Compaction` proved of the code before the PR too (etcd-grove `lean` `51547df02`), with the same proof file | `lean` | as in the file |
