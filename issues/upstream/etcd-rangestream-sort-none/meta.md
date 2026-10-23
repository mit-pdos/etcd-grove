# etcd-rangestream-sort-none

- **Finding**: `issues/etcd-rangestream-sort-none.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.7` (RangeStream is new in 3.7)
- **Branch**: `fix/etcd-rangestream-sort-none` in `~/etcd-fixes/etcd-rangestream-sort-none`, two commits:
  a8c642742 adds the tests, which fail there; 638081c75 is the fix. Force-pushed 2026-10-19 to `upamanyus/etcd` (replacing 5f0401a75); the issue's test link (`#L432-L471`) checked on GitHub: the test, doc comment to closing brace.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18; the code involved is unchanged
  since b25719d10, the earlier base)
- **State**: draft, to file as an issue linked to #22615 (2026-10-23): `issue.md`'s "Anything else" says #22615
  fixes it; no PR from this branch unless #22616 merges instead of #22615. Checked 2026-10-23: #22615's diff
  (head 017cb18c3) applied to `main` 22cc5d9ac with this branch's test commit a8c642742, go1.27.3:
  `TestKVGetStreamSortByCreateRevision` passes, `GetStreamToGetResponse` returning `Unimplemented: RangeStream
  does not support custom sort orders` (logged with a temporary `t.Logf`); `go test ./etcdserver/txn/
  ./etcdserver/api/v3rpc/` ok. With `main`'s `tests/integration/v3_grpc_test.go`, `TestV3RangeRequest/sort` fails
  under #22615 (its last case, `CREATE`/`NONE`, expected accepted by `RangeStream`); this branch's a8c642742 has
  the needed expectation change. Said in `../etcd-range-sort-none-limit/comment-22615.md`
- **Upstream issue**: —
- **Related PR**: etcd-io/etcd#22615 (2026-10-19, someone else's fix of etcd-io/etcd#22612, `etcd-range-sort-none-limit`)
  makes `IsDefaultOrdering` false for a non-key target with `NONE`, so `checkRangeStreamRequest` rejects these
  `RangeStream` requests, as this branch's fix does; it does not mention `RangeStream`. If it merges, this bug is
  fixed and this candidate is not needed; if #22616 merges instead, it is not
- **PR**: —

Commit messages to rewrite (drafts): `v3rpc: test RangeStream sorted by create revision without an order` (no body);
`v3rpc: reject RangeStream sorted by a non-key target without an order`, body "RangeStream can only stream in key
order, but it accepted a non-key sort target without an order, which the server sorts ascending by that target."

## Security

A wrong result for the requesting client only; no crash, hang, data loss or auth bypass. One more effect, not in
the issue: each chunk drops keys and the next restarts inside the keys already sent, so with keys created in reverse
key order the stream advances about two keys per chunk while each chunk stays near the chunk size target. Measured
at the base (2026-10-18, one member, `etcdctl get k l --sort-by=CREATE --stream`): 2000 keys of 1000-byte values,
2.0 MB by `get`, 267 MB streamed in 3.2 s (4442 key-values). The server's work stays proportional to what it sends,
which a client with read access can also cause with repeated `get`s of the whole range, and gRPC flow control paces
it by the client's reads; not a security report (the user's decision, 2026-10-18; the fix removes it too).

## Duplicates checked (2026-10-16, again 2026-10-18)

Searches (GitHub API): `RangeStream sort is:pr is:open` (0 results), `checkRangeStreamRequest` (#21631),
`RangeStream sort duplicate` (#21631, #21358, #12342); on 2026-10-18 `RangeStream sort` (adds #21791, #21748, #21261,
#12343, all closed), `RangeStream duplicate keys`, `checkRangeStreamRequest`. No duplicate, no open PR. Related, not
this bug: #21631 (merged, the RangeStream server, which added the check), #21358 (merged, the RangeStream client),
#21748 (closed, `TestKVGet`'s stream skips), #12342 (closed, 2020: OOM on large ranges, the motivation for
RangeStream). The finding's earlier links (#21631, 9acc0ebe3) stand.

## Why the fix works

At the base, `checkRangeStreamRequest` lets through `SortTarget: CREATE` with `SortOrder: NONE` because
`IsDefaultOrdering` is true for any target with `NONE`. `rangeStream` serves it as chunks: chunk 1 (limit 10) reads
`a`..`k` (limit + 1 = 11 keys in key order), `sortRangeResults` sorts them ascending by create revision (`k` .. `a`),
the response keeps 10 (`k` .. `b`, `More` set) and drops `a`; the next chunk starts after the chunk's last key, `b`, so
chunk 2 (limit 20) reads `c`..`k` again and sends them sorted (`k` .. `c`), `More` false. Result: 19 keys, `a`
missing. With the fix, a non-key target is rejected with `Unimplemented` whatever the order, as `ASCEND` and
`DESCEND` already were, so every accepted stream is in key order (`KEY` with `NONE` or `ASCEND`).

## Why the test shows the bug, not a misuse

`TestKVGetStreamSortByCreateRevision` (`tests/integration/clientv3/kv_test.go`, after `TestKVGetStreamCompactedError`,
the package's integration cluster) is the issue's example: 11 puts in reverse key order, then `Get` and `GetStream`
over `[a, z)`, keys-only, `WithSort(SortByCreateRevision, SortNone)`, an option set `clientv3` accepts for both
calls. It asserts the guarantee only: `GetStream` returns the keys `Get` returns, or is rejected with
`Unimplemented`, the server's answer to options RangeStream does not support. It does not assert which of the two,
so it holds for a server that streams the sort correctly too, and it compares with `Get` instead of a fixed order,
so it does not depend on what `NONE` means with a non-key target. With the fix the stream is rejected and the key
comparison is not reached.

## The two existing tests

Both mark a non-key sort with `NONE` as unsupported by RangeStream, in the tests commit:

- `TestV3RangeRequest` (`tests/integration/v3_grpc_test.go`), case "sort", request 5 (`CREATE`, `NONE`, 4 keys):
  `streamUnsupported` false to true, and its comment. The test streams every request not marked unsupported and
  requires `rangeStream` to succeed and match `Range`; over 4 keys (one chunk) the stream matched, so it passed at
  the base.
- `tests/common/kv_test.go`'s `rangeStreamSupports`, which mirrors `checkRangeStreamRequest` to skip the stream
  variants of `TestKVGetStream` the server rejects: it now also returns false for a non-key target. Its cases
  "all KVs ordered by create revision, unspecified sort order", "... by value, unspecified sort order" and its
  `--keys-only` variant now skip their stream variant.

Placed in the tests commit (all `*_test.go` changes first, the fix commit is the server change alone): at the tests
commit they pass (the stream variants skip, the base still accepts the request); at the fix commit they pass; with
the fix and without them they fail (run with `-overlay` of the base's test files: `TestV3RangeRequest` "Received
unexpected error" from `rangeStream`; `TestKVGetStream` fails the three cases above in each TLS variant). So the rule
"the tests commit fails, the fix commit passes" holds for the new test, and the two updates never fail at either
commit. The alternative, both updates in the fix commit, keeps that too; chosen against so that the fix commit is
only the change the PR's title names.

## Verification (go1.27.2 linux/amd64)

Example (issue): binaries built at the tests commit a8c642742 (non-test code identical to the base) with
`go build -ldflags "-X go.etcd.io/etcd/api/v3/version.GitSHA=22cc5d9ac"` in `server/` and `etcdctl/`, one member with
default flags on random local ports; output pasted into `issue.md`. 11 is the fewest keys: the first chunk has limit
10 (`initialStreamChunkLimit`), so 10 keys fit in one chunk. With etcd built at the fix (638081c75): `--stream` without
`--order` is rejected with the same `Unimplemented` error; without a sort target `--stream` gives `a b ... k`.

- At the tests commit a8c642742: `cd tests && go test ./integration/clientv3/ -run 'TestKVGetStreamSortByCreateRevision$'`
  fails: `expected: []string{"k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a"}`, `actual : []string{"k", "j",
  "i", "h", "g", "f", "e", "d", "c", "b", "k", "j", "i", "h", "g", "f", "e", "d", "c"}`. `go test ./integration/ -run
  'TestV3RangeRequest$'` ok; `go test -tags integration ./common/ -run 'TestKVGet$'` ok.
- At the fix commit 638081c75: `cd tests && go test ./integration/clientv3/ -run TestKVGetStream` ok;
  `go test ./integration/ -run 'TestV3RangeRequest$|TestV3RangeStream'` ok; `go test -tags integration ./common/ -run
  'TestKVGet$|TestKVGetStream'` ok (the stream variants named above skip); `cd server && go test
  ./etcdserver/api/v3rpc/` ok.
- `gofmt -l` on the changed files: clean; `go vet` on `server/etcdserver/api/v3rpc`, `tests/integration`,
  `tests/integration/clientv3`, `tests/common` (with `-tags integration`): clean.

Not run: `tests/e2e`, `make verify`, the robustness tests (their stream traffic sends no sort options), the whole
`tests/integration` module (shared machine).

Callers checked: no RangeStream caller in etcd sends a sort (`tools/benchmark` `range --stream`, the robustness
client and traffic, `etcdctl get --stream` only with a user's `--sort-by`); the gRPC proxy does not serve
RangeStream. No documentation of `RangeStream` or `GetStream` mentions sorting, so none to update.

## If a reviewer asks

- Behaviour change: `RangeStream` with a non-key target and `SortOrder: NONE` was accepted and is now rejected with
  `Unimplemented`. Such a stream was right only when the range fit in the first chunk (10 keys) or the keys were
  already in the target's order; clients wanting that sort use `Range` (as they must with `ASCEND`).
- Why not make `IsDefaultOrdering` false for a non-key target with `NONE`: `rangeLimit` uses it too, so that would
  also change unary `Range` (a separate bug, `etcd-range-sort-none-limit`: a unary range sorted by a non-key target
  with `NONE` and a limit returns the wrong keys; its candidate is `issues/upstream/etcd-range-sort-none-limit/`, not
  filed, revised in parallel). This PR stands alone and fixes only `RangeStream`; the two branches touch different
  files (this one `v3rpc/key.go` and three test files, the other `txn/range.go` and `txn/range_test.go`). The other
  bug does not change this example (the first chunk reads all 11 keys either way). Neither the issue nor the PR
  mentions the other.
- Why not stream such requests sorted: chunks start after a key, so the stream can only be in key order; sorting by
  another target needs the whole range, which RangeStream exists to avoid.
- Why the condition `r.SortTarget != pb.RangeRequest_KEY || !txn.IsDefaultOrdering(...)` rather than, e.g.,
  `SortOrder == DESCEND`: it keeps the existing check and adds the missing case; for `KEY` the two are the same.
- The error message still says "custom sort orders" (unchanged): a non-key target with `NONE` is sorted ascending by
  that target, so it is one.
- Backport: `release-3.7` has the same check (`key.go` line 173) and chunking (`initialStreamChunkLimit` 10); not run
  there. Earlier releases have no RangeStream.
