# Files for `notes/pr-verify/etcd-22215.md`

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `review22215_test.go` | The reviewer's stress test (package `backend`). Writers, shared and concurrent readers (`UnsafeRange` and `UnsafeForEach`, on present and missing buckets) and 1 ms commits run against 5 defrags. It passes under the race detector, so no race or wrong read was found. | etcd-io/etcd PR head `1fe4029cd` (upstream, not the fork) | `cp review22215_test.go <checkout>/server/storage/backend/ && cd <checkout>/server && go test -race -count=1 -run Review22215 ./storage/backend/` |
| `review22215-pr-1fe4029cd.log` | The tail of that run's output (`PASS`) | as above | as above |
