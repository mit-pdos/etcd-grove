# etcd-io/etcd#21968: files the report relies on

Revisions: the PR head `0190002950d54094dfc77726f9d7ce43964c84c4`; its upstream base `22d55b52acba4d981da3d139b6bc8912c7cadd18`;
the verified fork commit `0d0475c63` (`mit-pdos/etcd-grove` branch `pr-etcd-21968-goose-lean`, the PR applied to the fork's
`goose-lean` `09669450f`). Upstream at these revisions does not build with go1.27 (`x/net/http2`), so the upstream runs use
`GOTOOLCHAIN=go1.26.4` (its `go.mod` toolchain); the fork runs use `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `kvstore_compact_latest_test.go` | `TestStoreCompactLatestRevisionTwice`: compacting the head twice returns `nil` and a channel that closes; compacting below is `ErrCompacted`; the no-op holds after reopening the store; after a write the old head is `ErrCompacted` | PR head, base, fork branch | `cp kvstore_compact_latest_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -run TestStoreCompactLatestRevisionTwice ./storage/mvcc/` |
| `deterministic_compact_test.go` | `TestModelCompactLatestRevisionTwice`: the robustness model (`tests/robustness/model`) rejects the PR's success answer to a second compaction at the current revision (finding 1) | PR head (and base: same model) | `cp deterministic_compact_test.go <checkout>/tests/robustness/model/ && cd <checkout>/tests && go test -run TestModelCompactLatestRevisionTwice ./robustness/model/` |
| `probe.log` | the two tests above: PR head: store test passes, model test fails; base: store test fails with `ErrCompacted` on the second compaction, model test fails | PR head, base | as above |
| `probe.fork.log` | the store test passes on the verified fork branch | `0d0475c63` | as above, `GOTOOLCHAIN=go1.27.1` |
| `kvstore_compact_noop_edges_test.go` (the reviewer's) | `TestProbeCompactFreshStore` (negative and zero revisions, the first compaction), `TestProbeNoopBarrierAfterJob` (once a no-op's channel closes, the earlier compaction has finished), `TestProbeTombstoneHeadReopen` (a delete at the head, compacted, store reopened: `Compact(head)` succeeds) | PR head, base | `cp kvstore_compact_noop_edges_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -run TestProbe ./storage/mvcc/` |
| `review-probe.log` | the reviewer's tests: all pass on the PR head, all three fail on the base with `ErrCompacted` | PR head, base | as above |
