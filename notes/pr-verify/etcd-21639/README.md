# etcd-io/etcd#21639: files

Every test runs from a checkout's `tests/` directory, with `TMPDIR` set to a scratch directory:
`cp <file> <checkout>/tests/integration/ && cd <checkout>/tests && go test ./integration/ -run <Name> -count=1 -v`.
Upstream checkouts at the PR head and its base use `GOTOOLCHAIN=go1.26.4`; upstream `main` and
the fork use `GOTOOLCHAIN=go1.27.1`.

| File | What it shows |
|---|---|
| `txn_follower_auth_test.go` | Two integration tests (3 members, auth enabled, a non-root user runs `Then(Put(k2,"foo"), Get(k1))` through member 0, then `k2` is read on every member). `TestTxnFollowerAuthRangeRewritten`: the user may read/write `[k1,k3)`. `TestTxnFollowerAuthRangeRemoved`: the user may write `k2` only. |
| `pr-head.log` | At the PR head `cb56c8ad050d`: `RangeRewritten` FAILS, `k2` is `["foo" "v2" "v2"]`: the members without a waiting client check read permission on `"\x00"` instead of `k1`, are denied, and do not apply the put. `RangeRemoved` passes. |
| `upstream-base.log` | At the PR's base `3401a41e5` (upstream `main` before #21432): `RangeRemoved` FAILS, `k2` is `["v2" "foo" "foo"]`: the leader-side member denies `Get(k1)`, the others never see it (stripped) and apply the put. `RangeRewritten` passes. |
| `upstream-main.log` | At upstream `main` `b25719d10` (contains #21432): both pass. |
| `fork-pin.log` | At the fork's `goose-lean` pin `09669450f` (the verified code; contains #21432; same as `mit-pdos/etcd-grove` branch `pr-etcd-21639-goose-lean`, whose only commit is empty): both pass, and so does #21432's `TestTxnRangeRequestConsistency`. |
| `compacted-range.log` | #21432's `TestTxnRangeRequestConsistency` (the compacted-revision case of #18667, copied from upstream `main`'s `tests/integration/txn_range_consistency_test.go`): passes at the PR head, fails at its base. The PR fixes the case it targets. |
