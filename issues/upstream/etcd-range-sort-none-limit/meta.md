# etcd-range-sort-none-limit

- **Finding**: `issues/etcd-range-sort-none-limit.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.6`, `release-3.5`
- **Branch**: `etcd-range-sort-none-limit` in `~/etcd-fixes/etcd-range-sort-none-limit` (commit 596b66a38), not pushed
- **Base**: upstream `main` ea8b59433d82e8fc3f1365618740395e0028bd03 (2026-10-16)
- **State**: draft, revised after review (2026-10-16): the limit sweep as the example, the test compares limited with
  unlimited ranges, no comment on `rangeSortOrder`
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches: `IsDefaultOrdering`, `rangeLimit sort`, `SortNone limit`, `sort-by limit`. No duplicate. Related:
#20745 / #20746 (closed, unmerged: keep the limit for KEY/ASCEND), #21326 (merged 2026-04: the same optimization,
introduced `IsDefaultOrdering`; not the origin of the bug, which predates it), #6672 (2016: NONE sorts ascending).

## Verification

`TestRangeSortLimit` compares, for every target (KEY, VERSION, CREATE, MOD, VALUE) and order (NONE, ASCEND, DESCEND),
the range with limits 1-3 against the unlimited range. Failing on base (fix reverted): `cd server && go test
./etcdserver/txn/ -run TestRangeSortLimit` — the 4 non-key `*/NONE` subtests fail at limit 1 (`expected
[]string{"c"}, actual []string{"b"}`); the other 11 pass.

With the fix, all pass:

- `cd server && gofmt -l etcdserver/txn && go vet ./etcdserver/txn/ && go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/`
  (rerun at 596b66a38)
- `cd tests && go test ./integration/clientv3/ -run 'Range|Get|Sort'` and `cd tests && go test -tags integration
  ./common/ -run 'TestKVGet$|TestKVGetStream'` (run at 9f21608d3; 596b66a38 changes only a comment in `range.go`
  and the test)
- Base binaries (ea8b59433): `etcdctl get a d --sort-by=VERSION --keys-only` gives `c b a`, with `--limit=1` `b`, with
  `--limit=2` `c b` (the issue's sequence). With the fix (built at 9f21608d3), `--limit=1` gives `c`.

Not run: `tests/e2e` (`TestCtlV3GetTimeout` covers `--sort-by` without `--order`, needs `make build`), `make verify`.
