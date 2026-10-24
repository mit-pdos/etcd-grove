# Verification Artifacts for `etcd-io/etcd#22254`

Artifacts and logs accompanying [`notes/pr-verify/etcd-22254.md`](../etcd-22254.md) (`lint: enable unexported-return revive rule in pkg module`):

- [`wait_test.log`](wait_test.log): Output of `go test -v -race ./wait/...` in `/root/etcd-pr/etcd-22254/pkg` (commit `ff1051169ba665f0d0bdb78f759af5009c20bbc3` on `pr-etcd-22254-goose-lean`).
- [`flags_test.log`](flags_test.log): Output of `go test -v -race ./flags/...` in `/root/etcd-pr/etcd-22254/pkg`.
