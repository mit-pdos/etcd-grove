# etcd-backend-read-buffer-cache-stale-after-commit

## Security classification

Not a security report: no wrong result through etcd's API is known (see "Impact through mvcc" below), so no client
can use it to crash or hang a member, lose data or bypass auth. The issue says so ("I do not know of a wrong result
through etcd's API").

## Candidate

- **Finding**: `issues/etcd-backend-read-buffer-cache-stale-after-commit.md`
- **Target**: etcd-io/etcd, `main`; the cache dates from #12933 (9c82e8c72, 2021-05, v3.5), so `release-3.6` and
  `release-3.5` likely have it too (not checked)
- **Branch**: `fix/etcd-backend-read-buffer-cache-stale-after-commit` in `~/etcd-fixes/etcd-backend-read-buffer-cache-stale-after-commit`, two commits:
  d426dcdb9 (`storage/backend: test ConcurrentReadTx after a commit`) adds the test, which fails there; 1714a913c
  (`storage/backend: invalidate the ConcurrentReadTx cache on commit`) is the fix. Rebuilt 2026-10-18 on the new
  base, not pushed: the fork `upamanyus/etcd` still has the old single commit 29baf8d7e (off b25719d10, pushed
  2026-10-18) until the user approves
  `git -C ~/etcd-fixes/etcd-backend-read-buffer-cache-stale-after-commit push --force-with-lease=fix/etcd-backend-read-buffer-cache-stale-after-commit:29baf8d7e origin fix/etcd-backend-read-buffer-cache-stale-after-commit`.
  The issue's link (`backend_test.go#L443-L469`, the test from its doc comment to its closing brace) is to the new
  branch; check it on GitHub after the push.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18; `server/storage/backend` is
  unchanged since the previous base b25719d10)
- **State**: draft, revised to the 2026-10-18 standard of the upstream-report skill
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16, again 2026-10-18)

Searches: `txReadBufferCache`, `bufVersion`, `ConcurrentReadTx stale` (2026-10-16), `ConcurrentReadTx commit
stale` (2026-10-18). No duplicate, no open PR. Related: #17331 (closed, not planned: the stale-cache path copies
the buffer redundantly; not this bug), #12933 (merged as 9c82e8c72: introduced the cache and `bufVersion`), #13243
and #13259 (closed, unmerged: other designs of the shared read buffer), #17223 (closed: `UnsafeRange` panic during
shutdown; unrelated).

## Verification (go1.27.2 linux/amd64, in `server/`)

`TestConcurrentReadTxAfterCommit` (after `TestConcurrentReadTx`, in its style) is the issue's example: a temporary
backend (`betesting.NewTmpBackend`, batch interval one hour, so only `ForceCommit` commits); one batch transaction
creates the `Key` bucket and puts `abc`; a `ConcurrentReadTx` ranges over `[abc, \xff)` (a setup check that it
returns `abc` once; creating it fills the cache); `ForceCommit`; a new `ConcurrentReadTx` must return `abc` once.

- At the tests commit d426dcdb9 (`go test ./storage/backend/ -run TestConcurrentReadTxAfterCommit -count=1`):
  fails, `expected: []string{"abc"}`, `actual  : []string{"abc", "abc"}` (`after commit`).
- At the fix commit 1714a913c: passes; `go test ./storage/backend/... -count=1` ok, `go test ./storage/backend/
  -race -count=1` ok, `go test ./storage/mvcc/ -count=1` ok; `gofmt -l storage/backend` empty;
  `go vet ./storage/backend/...` clean.
- The finding's three reproductions (the racy delete, the pre-commit hook, the range duplicate), run through
  `go test -overlay` without adding them to the branch (at the base, overlaying the fix's `read_tx.go` and
  `backend.go` with the base's): all fail at the base (the racy one at trial 13), all pass with the fix (the racy
  one all 20000 trials).

Not run: `tests/integration`, `tests/e2e`, `make verify` (golangci-lint), benchmarks.

## Why the test shows the bug and not a misuse

Every call is the backend's documented API, used as mvcc uses it: writes through `BatchTx` under its lock, reads
through `ConcurrentReadTx` between `RLock` and `RUnlock`, `ForceCommit` (which the periodic batch commit does
anyway). The range with an end key is allowed only on a safe-range bucket ("known to never overwrite any key so
range is safe", `batch_tx.go`); `Key` is one, and the test writes `abc` once and never overwrites it. The
expectation is the test's own first read: nothing was written between the two reads, and a commit must not change
what the backend reads.

## Why the fix works

At the base: the write-back increments the read buffer's version to v; the first `ConcurrentReadTx` copies the
buffer (with `abc`) and caches it at v; `ForceCommit` writes `abc` into bolt and `readTx.reset` empties the buffer,
version still v; the second `ConcurrentReadTx` finds the cache at v, reuses the copy with `abc`, over a bolt
transaction that has `abc` too, and `UnsafeRange` returns bolt's entries followed by the buffer's. With the fix,
`reset` makes the version v+1, so the second `ConcurrentReadTx` copies the (empty) buffer. Both callers of `reset`
(`unsafeCommit`, and defrag's `finishDefrag`) hold `readTx.Lock`, and `ConcurrentReadTx` reads the version under
`readTx.RLock`, as for the write-back's increment.

## If a reviewer asks

- Cost: after every commit the next `ConcurrentReadTx` copies the read buffer once more; the buffer is empty right
  after a commit, so the copy is cheap.
- Why `readTx.reset` and not `unsafeCommit`: `reset` is where the buffer is emptied, and defrag calls it too.
  Equivalent alternative: a `txReadBuffer.reset` that resets and increments the version, next to the write-back's
  increment in `tx_buffer.go`; kept in `readTx.reset` as the one-line change.
- The comment edit: `ConcurrentReadTx`'s comment named only write-backs as making the cache stale; the fix adds
  "and commits". It can be dropped if the reviewer prefers the one-line change.
- Alternative: write back and commit in one `readTx.Lock` critical section in `batchTxBuffered.Unlock`. That closes
  only the racy window between the write-back and the commit, not the deterministic case (a cache filled before
  `ForceCommit` or the periodic commit), and holds readers off for the whole commit.
- Alternative: drop the cache when the buffer is reset (set `txReadBufferCache.buf` to nil). Needs
  `txReadBufferCache.mu` in the commit path; bumping the version reuses the existing staleness check.
- Impact through mvcc: mvcc's `store.Read` is the only caller of `ConcurrentReadTx`; it reads each revision with a
  single-key `UnsafeRange` (the buffer's entry first, so a revision committed and still in the stale copy reads the
  same value), its writers hold `revMu` exclusively over the batch `Unlock` (so no reader caches between the
  write-back and the commit of an mvcc write), and the pre-commit hook writes only `Meta`. So no wrong mvcc or API
  result is known; the stale copy can still return revisions that compaction deleted, but the index no longer
  names them. The deterministic case does happen in a running server (a read after a write, then the periodic
  commit); it is harmless there only because of the single-key reads.
- Backports: not checked or run on release branches.
