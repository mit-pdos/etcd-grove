# etcd-range-sort-none-limit

- **Finding**: `issues/etcd-range-sort-none-limit.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.6`, `release-3.5`
- **Branch**: `etcd-range-sort-none-limit` in `~/etcd-fixes/etcd-range-sort-none-limit` (commit 40a6c54fd), not pushed.
  `issue.md` links the test at `https://github.com/upamanyus/etcd/blob/etcd-range-sort-none-limit/...`, which
  resolves once the branch is pushed to the fork under that name.
- **Base**: upstream `main` ea8b59433d82e8fc3f1365618740395e0028bd03 (2026-10-16)
- **State**: draft, revised after review (2026-10-16): the limit sweep with three puts as the example, the test the
  same example, no root cause in the issue, no comment on `rangeSortOrder`
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches: `IsDefaultOrdering`, `rangeLimit sort`, `SortNone limit`, `sort-by limit`. No duplicate. Related:
#20745 / #20746 (closed, unmerged: keep the limit for KEY/ASCEND), #21326 (merged 2026-04: the same optimization,
introduced `IsDefaultOrdering`; not the origin of the bug, which predates it), #6672 (2016: NONE sorts ascending).

## Verification

`TestRangeSortLimit` is the issue's example: puts `c 1`, `b 2`, `a 3`, then a range over `[a, d)` sorted by CREATE
with order NONE, at limits 0, 1, 2 (want `c b a`, `c`, `c b`). Failing on base (fix reverted): `cd server && go test
./etcdserver/txn/ -run TestRangeSortLimit` — limit 1 gives `[]string{"b"}`.

With the fix, all pass:

- `cd server && gofmt -l etcdserver/txn && go vet ./etcdserver/txn/ && go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/`
  (rerun at 40a6c54fd)
- `cd tests && go test ./integration/clientv3/ -run 'Range|Get|Sort'` and `cd tests && go test -tags integration
  ./common/ -run 'TestKVGet$|TestKVGetStream'` (run at 9f21608d3; since then only a comment in `range.go` and the
  test changed)
- Base binaries (ea8b59433): after `put c 1; put b 2; put a 3`, `etcdctl get a d --sort-by=CREATE --keys-only` gives
  `c b a`, with `--limit=1` `b`, with `--limit=2` `c b`; `MODIFY` and `VALUE` with `--limit=1` give `b` too. With
  the fix (built at 40a6c54fd, `etcdctl-transcript.sh --bin`), the same sequence gives `c b a`, `c`, `c b`.

Not run: `tests/e2e` (`TestCtlV3GetTimeout` covers `--sort-by` without `--order`, needs `make build`), `make verify`.

## Review rounds

Round 1 (2026-10-16, a trial of step 10 after the user approved the issue): `check.py` clean. Reviewer edits:

- applied: permalinks for `sortRangeResults` and `rangeLimit` in the PR's root cause;
- applied: the `RangeStream` note says what changes for `RangeStream` (each chunk reads the rest of the range),
  with a permalink (it had a path relative to `server/etcdserver/`); its `RangeStream` sorting bug is
  `issues/etcd-rangestream-sort-none.md`, not mentioned in the PR;
- applied: the PR's manual test uses the issue's data (it sorted by version on keys all at version 1);
- applied: the second alternative says what #6672 did;
- rejected: drop `--limit=2` from the issue's example (the user chose the limit sweep).
