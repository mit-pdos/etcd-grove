# etcd-backend-read-buffer-cache-stale-after-commit

- **Finding**: `issues/etcd-backend-read-buffer-cache-stale-after-commit.md`
- **Target**: etcd-io/etcd, `main`; the cache dates from #12933 (9c82e8c72, 2021-05, v3.5), so `release-3.6` and
  `release-3.5` likely have it too (not checked)
- **Branch**: `etcd-backend-read-buffer-cache-stale-after-commit` in `~/etcd-fixes/etcd-backend-read-buffer-cache-stale-after-commit`
  (commit 29baf8d7e), not pushed. `issue.md` links
  the test at `https://github.com/upamanyus/etcd/blob/etcd-backend-read-buffer-cache-stale-after-commit/...`, which
  resolves once the branch is pushed to the fork under that name.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches (three, the finding was already searched earlier the same day): `txReadBufferCache`, `bufVersion`,
`ConcurrentReadTx stale`. No duplicate, no open PR. Related: #17331 (closed, not planned: the stale-cache path
copies the buffer redundantly; not this bug), #12933 (merged as 9c82e8c72: introduced the cache and `bufVersion`),
#13243 and #13259 (closed, unmerged: other designs of the shared read buffer).

## Verification

`TestConcurrentReadTxAfterCommit` is the issue's example: puts `abc` into the `Key` bucket, ranges `[abc, \xff)`
through a `ConcurrentReadTx` (which caches the read buffer), `ForceCommit`, ranges again through a new
`ConcurrentReadTx`. At the base: `cd server && go test ./storage/backend/ -run TestConcurrentReadTxAfterCommit
-count=1` fails with `actual: []string{"abc", "abc"}` ("after commit"). With the fix it passes.

With the fix, all pass:

- `cd server && go test ./storage/backend/... -count=1`, `go test ./storage/backend/ -race -count=1`,
  `go test ./storage/mvcc/ -count=1`
- `gofmt -l storage/backend` (empty), `go vet ./storage/backend/...`
- The finding's three reproductions (the racy delete, the pre-commit hook, the range duplicate), run through
  `go test -overlay` without adding them to the branch: all fail at the base (the racy one at trial 0) and pass
  with the fix (the racy one all 20000 trials).

Not run: `tests/integration`, `tests/e2e`, `make verify` (golangci-lint), benchmarks.

## If a reviewer asks

- Cost: after every commit the next `ConcurrentReadTx` copies the read buffer once more; the buffer is empty
  right after a commit, so the copy is cheap.
- Why `readTx.reset` and not `unsafeCommit`: `reset` is where the buffer is emptied, and defrag calls it too
  (both callers hold `readTx.Lock`, and `ConcurrentReadTx` reads the version under `readTx.RLock`).
- Alternative: write back and commit in one `readTx.Lock` critical section in `batchTxBuffered.Unlock`. That closes
  only the racy window between the write-back and the commit, not the deterministic case (a cache filled before
  `ForceCommit` or the periodic commit), and holds readers off for the whole commit.
- Alternative: drop the cache when the buffer is reset (set `txReadBufferCache.buf` to nil). Needs
  `txReadBufferCache.mu` in the commit path; bumping the version reuses the existing staleness check.
- Impact through mvcc: mvcc's `store.Read` is the only caller of `ConcurrentReadTx`; it reads each revision with a
  single-key `UnsafeRange` (the buffer's entry first, so a revision committed and still in the stale copy reads the
  same value), its writers hold `revMu` exclusively over the batch `Unlock`, and the pre-commit hook writes only
  `Meta`. So no wrong mvcc or API result is known; the stale copy can still return revisions that compaction
  deleted, but the index no longer names them.
- Backports: not checked or run on release branches.
