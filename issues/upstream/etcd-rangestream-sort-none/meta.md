# etcd-rangestream-sort-none

- **Finding**: `issues/etcd-rangestream-sort-none.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.7` (RangeStream is new in 3.7)
- **Branch**: `etcd-rangestream-sort-none` in `~/etcd-fixes/etcd-rangestream-sort-none` (commit 5f0401a75), not pushed.
  `issue.md` links the test at `https://github.com/upamanyus/etcd/blob/etcd-rangestream-sort-none/...`, which
  resolves once the branch is pushed: `git -C ~/etcd-fixes/etcd-rangestream-sort-none push origin etcd-rangestream-sort-none`.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches (GitHub API): `RangeStream sort is:pr is:open` (0 results), `checkRangeStreamRequest` (#21631),
`RangeStream sort duplicate` (#21631, #21358, #12342). No duplicate, no open PR. Related, not this bug: #21631 (merged,
the RangeStream server, which added the check), #21358 (merged, the RangeStream client), #12342 (closed, 2020: OOM on
large ranges, the motivation for RangeStream). The finding's earlier links (#21631, 9acc0ebe3) stand.

## Verification

Example (issue): base binaries built from b25719d10 (`go build -ldflags "-X go.etcd.io/etcd/api/v3/version.GitSHA=b25719d10"`
in `server/` and `etcdctl/`), one member with default flags on random local ports; 11 keys put in reverse key order,
then `get a z --sort-by=CREATE --keys-only` (`k j ... a`), the same with `--stream` (`k j i h g f e d c b k j i h g f e
d c`), the same with `--stream --order=ASCEND` (`Unimplemented`). 11 is the fewest keys: the first chunk has limit 10
(`initialStreamChunkLimit`), so 10 keys fit in one chunk. With the fix (server rebuilt at the fix): `--stream` without
`--order` is rejected with the same `Unimplemented` error; without a sort target `--stream` gives `a b ... k`.

`TestKVGetStreamSortByCreateRevision` (`tests/integration/clientv3/kv_test.go`) is the example's stream requests: same
puts, `GetStream` over `[a, z)` keys-only sorted by create revision with `SortAscend` and `SortNone`, both expected
`Unimplemented`. On base (fix reverted): `cd tests && go test ./integration/clientv3/ -run
'TestKVGetStreamSortByCreateRevision$'` fails in `SortNone` with `GetStream returned [k j i h g f e d c b k j i h g f e d
c]`; `SortAscend` passes. With the fix, all pass:

- `cd tests && go test ./integration/clientv3/ -run TestKVGetStream` (ok)
- `cd server && go test ./etcdserver/api/v3rpc/` (ok)
- `cd tests && go test ./integration/ -run 'TestV3RangeRequest$|TestV3RangeStream'` (ok)
- `cd tests && go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'` (ok; the stream variants of
  "ordered by create revision, unspecified sort order" and "ordered by value, unspecified sort order" now skip)
- `gofmt -l` on the changed packages: clean; `go vet` on `server/etcdserver/api/v3rpc`, `tests/integration`,
  `tests/integration/clientv3`, `tests/common` (with `-tags integration`): clean

Not run: `tests/e2e`, `make verify`, the robustness tests (their stream traffic sends no sort options).

## If a reviewer asks

- Behaviour change: `RangeStream` with a non-key target and `SortOrder: NONE` was accepted and is now rejected with
  `Unimplemented`. Such a stream was right only when the range fit in the first chunk (10 keys) or the keys were already
  in the target's order; clients wanting that sort use `Range` (as they must with `ASCEND`).
- Why not make `IsDefaultOrdering` false for a non-key target with `NONE`: `rangeLimit` uses it too, so that would also
  change unary `Range` (the separate bug `etcd-range-sort-none-limit`, a unary range sorted by a non-key target with
  `NONE` and a limit returning the wrong keys; its candidate is `issues/upstream/etcd-range-sort-none-limit/`, not yet
  filed). This PR stands alone and fixes only `RangeStream`; with both fixes applied, the two changes do not conflict.
  The other bug does not change this example (the first chunk reads all 11 keys either way).
- Why not stream such requests sorted: chunks start after a key, so the stream can only be in key order; sorting by
  another target needs the whole range, which RangeStream exists to avoid.
- Why the two test expectation changes: `TestV3RangeRequest` marked its `NONE`/`CREATE` request as supported by
  RangeStream (4 keys, one chunk, so the stream matched `Range`); `tests/common`'s `rangeStreamSupports` mirrors the
  server's check.
- Backport: `release-3.7` has the same check (`key.go` line 173) and chunking (`initialStreamChunkLimit` 10); not run
  there. Earlier releases have no RangeStream.
- Security: a wrong result for the requesting client only; no crash, hang, data loss or auth bypass.
