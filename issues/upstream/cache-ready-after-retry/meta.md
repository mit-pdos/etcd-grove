# cache-ready-after-retry

- **Finding**: `issues/cache-ready-after-retry.md`
- **Target**: etcd-io/etcd, `main` (the `cache` module, `go.etcd.io/etcd/cache/v3`)
- **Branch**: `fix/cache-ready-after-retry` in `~/etcd-fixes/cache-ready-after-retry`, two commits: 4c9743e0e
  (`cache: test readiness after a compaction resync`) adds the test, which fails there; 27352098d (`cache: initialize
  the demux before registering the store watcher`) is the fix. Rebuilt 2026-10-18 on the new base; **not pushed**:
  the fork's `fix/cache-ready-after-retry` still has the old single commit fcfb43c88 (off b25719d10, with the earlier
  test `TestCacheReadyAfterWatchRetry`), so the links in `issue.md` resolve only after a force-push the user approves:
  `git -C ~/etcd-fixes/cache-ready-after-retry push --force-with-lease=fix/cache-ready-after-retry:fcfb43c889937a4227eb56d87329ca25873a966c origin fix/cache-ready-after-retry`.
  Then check on GitHub that `cache/cache_test.go#L509-L544` is the test, doc comment to closing brace. The fork's
  older draft branch `cache-ready-after-retry` (64313a1f8) is left as it was.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18). `cache/` is unchanged since the
  previous base b25719d10 (`git diff b25719d10 22cc5d9ac -- cache/` is empty), so the permalinks' lines are the same.
- **State**: draft (revised 2026-10-18 to the current skill)
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16, re-checked 2026-10-18)

Earlier searches (the finding's front matter) plus PR #22408 read, and searches `cache ready retry watch is:open`,
`demux Init purge`. No duplicate. Related:

- #22408 (pr open, "cache: apply the configured back-off and Get timeout"; still open 2026-10-18, head baf38e97b, not
  in `main`): the same retry loop (`getWatchLoop`, `get`, `newCache`), not this bug; it does not touch `watch`,
  `watchEvents` or `demux.Init`. No textual conflict (its tests go at the end of `cache_test.go`, this one after
  `TestCacheCompactionResync`). If it lands, the test still works: its default `InitialBackoff` stays 50 ms, under
  the test's one second of fake time.
- #20691 (pr closed, "cache: make demux maintain min/max revision range") and #20614 (pr closed, "cache: make the
  cache progress-aware"): where the demux's `Init`/purge come from (not checked further).
- #21536 (issue closed): a different cache bug (Get with revision gaps).

## Security

The cache is a client-side library; a cache that stays not ready blocks that client's `WaitReady` and `Watch`, not an
etcd member, and loses no data. Not a security report.

## Why the fix works

At the base, `watch(rev)` creates one `sync.Once` and loops: register a store watcher at `rev`, open the upstream
watch, and on its first response run `demux.Init(rev)` and `ready.Set()` once. In the test: the first watch
(from 6) runs `Init(6)` on a fresh demux (`minRev = 6`, no purge) and sets ready. The compaction cancels it: `watch`
returns the error, `getWatchLoop` backs off and retries. The retry's Get returns 10, `watch(11)` registers a store
watcher at 11, and the first response runs `Init(11)`: `minRev != 0` and `maxRev == 0` (no event seen), so the demux
is purged, which stops that store watcher. `ready.Set()` runs, `applyStorage` sees the stopped watcher and returns
nil, `watchEvents` resets ready and returns nil, and `watch` loops with the spent `Once`: a new store watcher and a
new upstream watch, events flow, but ready is never set again (it was set for an instant, which is why the test
checks the settled state, after `synctest.Wait`, not `WaitReady`). A demux that saw events purges the same way when
`rev != maxRev + 1`; after a compaction cancels the watch, the retry's Get is always past `maxRev + 1`.

With the fix, `watch` calls `Init(rev)` once on entry, before the first store watcher is registered: the purge stops
only watchers of earlier upstream watches, and the first response only sets ready.

## The test, and why it is legitimate

`TestCacheReadyAfterCompactionResync`, right after `TestCacheCompactionResync`, with the package's `mockWatcher` and
`kvStub`, under `synctest` (as `TestWaitTillRevisionTriggersProgressRequests` is): Gets at 5 and 10; created
notification; the cache is ready (the setup check that the scenario started); `errorCompacted(10)` (the package's
helper, the response etcd sends when it cancels a watch for a compaction); created notification; one second of fake
time (the retry's 50 ms back-off); `synctest.Wait`; the cache must be ready. It asserts only readiness, which
`Ready`'s doc ties to "the snapshot has been loaded and the first watch has been confirmed".

Changed from the previous draft (`TestCacheReadyAfterWatchRetry`, Get at 5, event at 6, a cancel with the made-up
reason "canceled", retry Gets at 6 and 7): etcd's server cancels an established watch only for a compaction (its
other cancels answer the create request; the client library can also end a watch with an error when it cannot resume
its stream), and after a compaction the retry's Get is always past the last event, so the earlier passing variant
(retry Get at 6) needs a cancel the server does not send. The compaction case is what etcd does, needs no event, and is
the scenario `TestCacheCompactionResync` already runs (which passes at the base because it checks `WaitForRevision`,
not readiness).

## Verification (go1.27.2 linux/amd64, in `cache/` unless said)

- At the tests commit 4c9743e0e, `go test . -run 'TestCacheReadyAfterCompactionResync$' -count=1 -v`:

  ```
  === RUN   TestCacheReadyAfterCompactionResync
  getWatch failed, will retry after 50ms: etcdserver: mvcc: required revision has been compacted
      cache_test.go:541: cache not ready after the resync
  getWatch failed, will retry after 50ms: context canceled
  --- FAIL: TestCacheReadyAfterCompactionResync (0.00s)
  FAIL
  FAIL	go.etcd.io/etcd/cache/v3	0.018s
  ```

  `-count=20 -race`: fails 20 of 20.
- At the fix commit 27352098d: the test passes (`-count=20 -race` too); `go test ./... -count=1` ok; `gofmt -l .`
  empty; `go vet ./...` clean. In `tests/`: `go test ./integration/ -run '^(TestCache|TestWatch$|TestGet$|TestWithPrefixGet$)'`
  (the cache's integration tests, `tests/integration/cache_test.go`) ok.
- A temporary test (2026-10-18, run by `go test -overlay` with `cache.go` at the base, not kept): an event at 6
  before the failure, then a retry Get at 6, 7 (after a cancel) or 10 (after `errorCompacted(10)`): ready at the base
  only for 6; ready for all three with the fix (the `rev != maxRev + 1` purge).

Not run: the rest of `tests/`, `make verify`. Not reproduced against a real cluster.

## check.py

`python3 -I .claude/skills/upstream-report/check.py cache-ready-after-retry` (2026-10-18): no FAIL. WARNs decided:

- the comment added in `watch` (two WARN lines): kept, it states the ordering the code needs (a purge stops every
  registered watcher), which the code does not show;
- `issue: names code the fix touches: ['watch']`: the plain word (the upstream watch), not the function;
- `pr: 104 words`: kept; the approved raft candidates' PRs are 117 and 136 words.

## If a reviewer asks

- Why `demux.Init` can move out of the first response: its argument is `rev`, known when `watch` is entered; the
  first response now gates only `ready.Set`. With `Init` before the first `Register`, a purge stops only watchers of
  earlier `watch` calls (the previous store watcher is already unregistered; `Cache.Watch` watchers would have been
  purged by the same `Init` at the first response anyway, just later). A `Cache.Watch` that passed `WaitReady` before
  the failure and registers after the early `Init` is no longer purged: it is lagging, and the resync loop cancels it
  as compacted if its start revision is below the new `minRev`, or serves it from history otherwise (code reading).
- Why not a new `sync.Once` per loop iteration: after the purge `maxRev` is 0, so each iteration's `Init` takes the
  `maxRev == 0` branch, purges again and stops that iteration's store watcher; `watch` reopens the upstream watch in
  a loop. Dropping the `Once` and calling `Init`/`ready.Set` on every first response loops the same way, with
  readiness flapping. Returning an error from `watch` when the store watcher is stopped (a fresh Get) purges again
  for the same reason (code reading, not run).
- One `Once` per `watch` call is enough once `Init` is out of the loop: nothing else purges the demux (`Purge` and
  `Compact` are called only from tests), and the store watcher is otherwise stopped only when it lags behind the
  demux history, in which case the restarted upstream watch replays revisions `Broadcast` rejects as stale, so
  `watch` returns an error and the cache retries from a new Get with a new `Once`.
- The added comment in `watch` says why the order matters; drop it if the reviewer prefers.
- `Ready`'s doc ("the first watch has been confirmed") still holds: ready is set on the first response of the
  upstream watch.
- Backports: `release-3.7` has the same `watch`, `watchEvents` and `demux.Init`, and both commits merge cleanly
  onto it (`git merge-tree`, 2026-10-18; not built or run there); `release-3.6` has no cache. The maintainers' call.
