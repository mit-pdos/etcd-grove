# Files for the verification of etcd PR #22499

Report: `notes/pr-verify/etcd-22499.md`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `backend_test.go` | The PR's own unit tests (`server/storage/backend_test.go` at the PR head 3402a44f): the snap directory is synced exactly once after the rename, an injected sync error fails the open with no backend, a missing snapshot does not sync. They inject through the package variable `syncSnapDir`. | `mit-pdos/etcd-grove` branch `pr-etcd-22499-goose-lean` (f87e747cb), and the PR head | `cp backend_test.go <checkout>/server/storage/ && cd <checkout>/server && GOTOOLCHAIN=go1.27.1 go test -race -count=1 -run TestOpenSnapshotBackend ./storage/` |
| `backend_test.log` | That command's output on the fork branch: all three pass under `-race`. | as above | as above |
