# cache-ready-after-retry

- **Finding**: `issues/cache-ready-after-retry.md`
- **Target**: etcd-io/etcd, `main` (the `cache` module, `go.etcd.io/etcd/cache/v3`)
- **Branch**: `fix/cache-ready-after-retry` in `~/etcd-fixes/cache-ready-after-retry` (commit fcfb43c88), pushed 2026-10-18 to `upamanyus/etcd`
  (`https://github.com/upamanyus/etcd/tree/fix/cache-ready-after-retry`), the branch the links in `issue.md` name. The fork's older
  draft branch `cache-ready-after-retry` (64313a1f8) is left as it was.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Earlier search (2026-10-16, the finding's front matter) plus, this run: PR #22408 read, and searches `cache ready
retry watch is:open`, `demux Init purge`. No duplicate. Related:

- #22408 (pr open, "cache: apply the configured back-off and Get timeout"): the same retry loop (`getWatchLoop`,
  `get`, `newCache`), not this bug; it does not touch `watch`, `watchEvents` or `demux.Init`. The two changes do not
  conflict textually.
- #20691 (pr closed, "cache: make demux maintain min/max revision range") and #20614 (pr closed, "cache: make the
  cache progress-aware"): where the demux's `Init`/purge come from (not checked further).
- #21536 (issue closed): a different cache bug (Get with revision gaps).

## Verification

`TestCacheReadyAfterWatchRetry` (in `cache/cache_test.go`, next to `TestCacheCompactionResync`, with its
`mockWatcher` and `kvStub`, under `synctest` so the end state is deterministic) is the issue's example: Get at 5,
watch from 6, created, event at 6; the watch is canceled; the retry's Get returns 6 or 7, the retried watch is
created; the cache must be ready. At the base, revision 7 fails (`cache not ready after the retried watch`), 30 of
30 runs with `-race`; revision 6 passes. With the fix both pass (30 of 30 with `-race`).

Commands (in `cache/`):

- `go test . -run TestCacheReadyAfterWatchRetry -count=1 -v` with `cache.go` at the base: FAIL (revision 7), with the
  fix: PASS; `-count=30 -race`: same.
- `go test ./... -count=1`: ok.
- `gofmt -l .`: nothing; `go vet ./...`: clean.
- Also run once, not kept in the test: the variant where the first watch receives no event (retry Gets at 5 and 6)
  fails at the base for both and passes with the fix (the `maxRev == 0` purge).

Not run: anything outside the `cache` module (the change does not leave it), `tests/integration` cache tests,
`make verify`. Not reproduced against a real cluster.

## check.py

Clean (no FAIL). WARNs decided: the comment added in `watch` is kept (it states the ordering constraint, which the
code does not); `watch` in the issue is the plain word (the upstream watch), not the function name.

## If a reviewer asks

- Why `demux.Init` can move out of the first response: its argument is `rev`, known when `watch` is entered; the
  first response now gates only `ready.Set`. With `Init` before the first `Register`, a purge stops only watchers of
  earlier `watch` calls (the previous store watcher is already unregistered, and `Cache.Watch` watchers would have
  been purged by the same `Init` on the first response anyway, just later).
- Why not a new `sync.Once` per loop iteration: after the purge `maxRev` is 0, so each iteration's `Init` takes the
  `maxRev == 0` branch, purges again and stops that iteration's store watcher; `watch` reopens the upstream watch in
  a loop. Dropping the `Once` and calling `Init`/`ready.Set` on every first response loops the same way, with
  readiness flapping.
- One `Once` per `watch` call is enough once `Init` is out of the loop: nothing else purges the demux (`Purge` and
  `Compact` are called only from tests), and the store watcher is otherwise stopped only when it lags behind the
  demux history, in which case the restarted upstream watch replays revisions `Broadcast` rejects as stale, so
  `watch` returns an error and the cache retries from a new Get with a new `Once`.
- `TestCacheCompactionResync` already goes through this path (its first watch saw no event, so the retry purges)
  and passes at the base because it checks `WaitForRevision`, not readiness.
- The added comment in `watch` says why the order matters; drop it if the reviewer prefers.
- Security: the cache is a client-side library; a cache that stays not ready blocks that client's `WaitReady` and
  `Watch`, not an etcd member, and loses no data. Judged not a security report.
- Backports: not checked on release branches.
