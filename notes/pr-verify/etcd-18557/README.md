# Files for `notes/pr-verify/etcd-18557.md`

Revisions: PR head = etcd-io/etcd `749efe80c6b398a071ce1b83ea197858e17879e0`; upstream base =
`0167cb307510f58129ff365fa12f145c42b10104` (its merge base with `main`); fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-18557-goose-lean` (`02240ef89`: the fork's `goose-lean`
`09669450f` plus the PR). Go toolchain: `go1.26.4` on the PR head (its `go.mod` names go1.24),
`go1.27.1` on the fork branch. Run with `TMPDIR` on a disk with room.

All tests are integration tests of `tests/integration/clientv3/experimental/recipes` (package
`recipes_test`): `cp <file> <checkout>/tests/integration/clientv3/experimental/recipes/ && cd
<checkout>/tests && go test -count=1 -v -run '<names>' ./integration/clientv3/experimental/recipes/`.

| File | What it shows | Runs against |
|---|---|---|
| `v3_queue_uint64_test.go` | `TestUint64PrQueueOrderAtSixDigits`: after `EnqueueUint64` at 99999 and at 100000, `Dequeue` returns priority 100000 first. `TestUint64PrQueueEnqueueOverwrites`: three items at 10000, one at 100000, then one more at 10000: 4 items after 5 enqueues (the last put overwrote `prq/10000/0000000000000001`) | PR head and fork branch: both fail |
| `v3_queue_uint64_test-pr-head.log` | the two tests' failures on the PR head, with the PR's own two `TestUint64PrQueue*` tests passing (logger lines removed) | PR head |
| `v3_queue_uint64_probe_test.go` | the reviewer's probes. `TestProbeRepeatedOverwrite`: with three items at 100000, three enqueues at 10000 all take the same key (4 items after 6 enqueues). `TestProbeMixEnqueue`: after `EnqueueUint64(.., 100001)`, two `Enqueue(.., 10000)` (the `uint16` one) overwrite each other. `TestProbeTimestamps`: 19-digit nanosecond timestamps mixed with a small priority are fine (passes) | PR head |
| `probe_test-pr-head.log` | the probes' output on the PR head | PR head |
| `enqueueuint64-020d.patch`, `v3_queue_uint64_test-020d.log` | with `EnqueueUint64` printing `%020d`, all four `TestUint64PrQueue*` tests pass (a queue that only uses `EnqueueUint64`) | PR head + patch (`git apply`) |
| `newSequentialKV-slash.patch`, `v3_queue_uint64_tests-newSequentialKV-fix.log` | with `newSequentialKV` looking up the last key under `prefix + "/"`, the overwrite tests and the probes pass and the existing queue tests still pass; the order test still fails (that needs a fixed width) | PR head + patch, with both test files |
