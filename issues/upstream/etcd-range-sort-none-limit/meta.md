# etcd-range-sort-none-limit

- **Finding**: `issues/etcd-range-sort-none-limit.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.6`, `release-3.5`
- **Branch**: `fix/etcd-range-sort-none-limit` in `~/etcd-fixes/etcd-range-sort-none-limit`, two commits (2026-10-18):
  1f10b22ed adds the test, which fails there; 6cb3f6108 is the fix. Force-pushed 2026-10-19 to `upamanyus/etcd` (replacing 972c22ce2); the issue's test link (`#L279-L310`) checked on GitHub: the test, doc comment to closing brace.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18; `range.go` unchanged since
  ea8b59433, the base of the first version)
- **State**: draft, rebuilt to the 2026-10-18 standard (two commits, `etcdserver:` prefix, test in `txn_test.go`)
- **Upstream issue**: —
- **PR**: —

Commit messages (drafts for the user to rewrite):

- `etcdserver: test range sorted by a non-key target with a limit` (no body)
- `etcdserver: read the whole range before sorting with SortOrder NONE`, body: "A range with a non-key sort target
  and SortOrder NONE is sorted ascending, but its read stopped at the limit as if it were unsorted."

## Duplicates checked (2026-10-16; not re-run for the 2026-10-18 rebuild)

Searches: `IsDefaultOrdering`, `rangeLimit sort`, `SortNone limit`, `sort-by limit`. No duplicate. Related:
#20745 / #20746 (closed, unmerged: keep the limit for KEY/ASCEND), #21326 (merged 2026-04: the same optimization,
introduced `IsDefaultOrdering`; not the origin of the bug, which predates it), #6672 (2016: NONE sorts ascending).

## Why the fix works

At the base, `executeRange` asks mvcc for `rangeLimit(r)` keys: the request's limit plus one unless
`IsDefaultOrdering(r.SortTarget, r.SortOrder)` is false (or revision filters are set). `IsDefaultOrdering` is true for
any target with `NONE`, so for the issue's `CREATE`/`NONE`, limit 1, mvcc reads `a`, `b` (key order). Then
`sortRangeResults` turns `NONE` into `ASCEND` for a non-key target and sorts those two by create revision (`b` 3,
`a` 4); the response keeps the first, `b`. `c` (create revision 2) was never read. With the fix, `rangeLimit` asks
`IsDefaultOrdering` about the order the results are sorted in (`rangeSortOrder`: `ASCEND` here), which is false, so
mvcc reads the whole range, the sort sees `c`, `b`, `a`, and the response is `c`. The rule moved from
`sortRangeResults` into `rangeSortOrder` so that both decisions use it. `KEY` with `NONE`/`ASCEND` keeps the limit
as before; `DESCEND` and non-key `ASCEND` already dropped it.

The test is the issue's example: three puts, one range request with the same target and order, varied only in its
limit; nothing else is set (the harness is the package's `setup`, an mvcc store), so it shows the server's answer to
an ordinary request, not a misuse.

## Verification (go1.27.2 linux/amd64)

- At the tests commit 1f10b22ed (`cd server && go test ./etcdserver/txn/ -run 'TestRangeSortLimit$'`): fails at
  limit 1, `expected: []string{"c"}`, `actual  : []string{"b"}`.
- At the fix commit 6cb3f6108: the test passes; `go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/` ok;
  `gofmt -l etcdserver/txn` empty; `go vet ./etcdserver/txn/` clean.
- Binaries at the base 22cc5d9ac (`go build` in `server/` and `etcdctl/` with `-X ...version.GitSHA=22cc5d9ac`, a
  single member on free ports): the issue's commands give `c b a`, `b` for `--limit=1`, `c b` for `--limit=2`, and
  `c` with `--order=ASCEND --limit=1` (the outputs in `issue.md`, pasted from this run). The same commands against
  `etcd` built at 6cb3f6108 give `c b a`, `c`, `c b`.
- Earlier, at ea8b59433 with the same code (2026-10-16): `cd tests && go test ./integration/clientv3/ -run
  'Range|Get|Sort'` and `go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'` passed; `MODIFY` and
  `VALUE` with `--limit=1` give `b` too on the base. Not re-run at 22cc5d9ac.

Not run: `tests/e2e` (`TestCtlV3GetTimeout` covers `--sort-by` without `--order`, needs `make build`), `make verify`
(golangci-lint).

## Review (2026-10-18)

The earlier rounds (2026-10-16) set the issue (the limit sweep with three puts, the user's choice), kept `RangeStream`
out of the issue and the PR (the user's decision), and dropped a comment on `rangeSortOrder`. The rebuild to the
current standard:

- two commits (tests, then the fix), subject 67 characters with etcd's `etcdserver:` prefix (was 79,
  `etcdserver/txn:`), the fix's body one sentence (was six lines);
- the test moved from a new `range_test.go` into `txn_test.go`, after `TestCheckRange`, next to the package's other
  `Range` test and its `setup` (no new file and license header); `require.Equalf` for its formatted message
  (testifylint's formatter rule, which etcd enables);
- issue: the expectation says "should"; the test link has its lines and the base; outputs re-run at 22cc5d9ac;
- PR: names the assumption `rangeLimit` makes; the standard line on the two commits.

Maintainer review by hand: `rangeLimit` has one caller (`executeRange`); `IsDefaultOrdering` is unchanged, so its
other callers (`checkRangeStreamRequest`, `tests/common/kv_test.go`) behave as before. No comment or doc claims the
old behavior. No new bug found.

## If a reviewer asks

- Cost: these requests now read the whole range before sorting, as the same request with `SortOrder: ASCEND`
  already does.
- `RangeStream` (not mentioned upstream, the user's decision): it accepts `NONE` with a non-key target and runs each
  chunk through `executeRange`; with this fix each chunk reads the rest of the range instead of `limit + 1` keys.
  Its answers are wrong either way (its next chunk starts after the last key in sort order, not key order), which is
  a separate bug (`issues/etcd-rangestream-sort-none.md`; its branch rejects such requests in `key.go` and touches no
  file this branch does).
- Why not one more condition in `rangeLimit` (`r.SortTarget != pb.RangeRequest_KEY ||` ...): it works, but would
  restate the "`NONE` means `ASCEND` for a non-key target" rule that `sortRangeResults` applies; the helper keeps the
  two decisions on one rule. Not run.
- Why not have `etcdctl` send `ASCEND` when `--sort-by` is given without `--order`: that fixes `etcdctl` only;
  other clients sending `NONE` with a limit would still get the wrong keys.
- Why not make `NONE` mean no sorting, as `rpc.proto` documents: that would undo #6672, which made a non-key target
  with no order sort ascending; `TestV3RangeRequest` ("sort ASCEND by default") and `TestCtlV3GetTimeout`
  (`--sort-by=CREATE`) test that behavior.
- Backports: `release-3.6` (`executeRange`) and `release-3.5` (`applierV3backend.Range`) have the same condition
  (`r.SortOrder != NONE`); not run there.
