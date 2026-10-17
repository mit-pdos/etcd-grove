# etcd#22297: files the report relies on

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `resync_delay_probe_test.go` | `resyncDelay` returns the documented delay, always positive and accepted by `time.Ticker.Reset`, over edge values of all three arguments: zero, negative and extreme durations (`math.MinInt64` .. `math.MaxInt64`) and counts (`math.MinInt` .. `math.MaxInt`) | the PR head `8a7b19d0c` (upstream checkout); also passes on `mit-pdos/etcd-grove` branch `pr-etcd-22297-goose-lean` | `cp resync_delay_probe_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -run TestResyncDelayProbe -v ./storage/mvcc/` |
| `resync_delay_probe.log` | that test's output at the PR head (PASS) | PR head `8a7b19d0c`, go1.27.1, linux/amd64 | as above |
