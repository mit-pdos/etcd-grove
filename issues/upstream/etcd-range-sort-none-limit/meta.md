# etcd-range-sort-none-limit

- **Finding**: `issues/etcd-range-sort-none-limit.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.6`, `release-3.5`
- **Branch**: `etcd-range-sort-none-limit` in `~/etcd-fixes/etcd-range-sort-none-limit` (commit 9f21608d3), not pushed
- **Base**: upstream `main` ea8b59433d82e8fc3f1365618740395e0028bd03 (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches: `IsDefaultOrdering`, `rangeLimit sort`, `SortNone limit`, `sort-by limit`. No duplicate. Related:
#20745 / #20746 (closed, unmerged: keep the limit for KEY/ASCEND), #21326 (merged 2026-04: the same optimization,
introduced `IsDefaultOrdering`; not the origin of the bug, which predates it), #6672 (2016: NONE sorts ascending).

## Verification

Failing on base (fix reverted): `cd server && go test ./etcdserver/txn/ -run TestRangeSortLimit` — the 4 `*/NONE`
subtests fail with `expected "c", actual "b"`; `*/ASCEND` pass.

With the fix, all pass:

- `cd server && gofmt -l etcdserver/txn && go vet ./etcdserver/txn/ && go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/`
- `cd tests && go test ./integration/clientv3/ -run 'Range|Get|Sort'`
- `cd tests && go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'`
- Built `etcd`/`etcdctl` at base and with the fix; the `etcdctl` sequence in `issue.md` returns `b` on base, `c` with
  the fix.

Not run: `tests/e2e` (`TestCtlV3Get*`, needs `make build`), `make verify`.
