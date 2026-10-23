# bbolt-commit-meta-error-frees-reader-pages: upstream candidate

- **Target**: etcd-io/bbolt.
- **Base**: upstream `main` a4ef19710eb7ddc41fd1155336baf331b5c57ba8 ("Update changelog for bucket related
  protection", 2026-10-15). `Tx.Commit`, `Tx.writeMeta`, `Tx.rollback` and `DB.meta` unchanged since v1.5.0 (the
  finding's lines moved by a few: `rollback` is `tx.go:322-343`, the meta write `tx.go:605-619`).
- **Branch**: `fix/bbolt-commit-meta-error-frees-reader-pages` in `~/etcd-fixes/bbolt-commit-meta-error-frees-reader-pages`
  (clone `~/etcd-bbolt`, remotes `upstream` etcd-io/bbolt, `origin` upamanyus/bbolt):
  - `406c281` tx: test reader snapshot after a failed commit's meta write (`db_whitebox_test.go`)
  - `eb2b2e0` tx: keep a failed commit's freed pages pending if its meta is current (`tx.go`)
  - No changelog commit: bbolt's `CHANGELOG/` entries are added in commits of their own, mostly by the
    maintainers after merging (the last 15 changelog commits touch no code but two).
- **Issue form**: bbolt has no issue template; `issue.md` is free-form prose, no headings (the 2026-10-23 review).
  At the user's request (2026-10-23), "Anything else" explains the cause (`rollback` reloading the new meta's
  freelist), against the skill's symptom-only rule; no code link there (the PR has them), so `check.py` warns
  (length, the name `rollback`) but does not fail.
- **State**: draft, branch pushed (2026-10-23) to the fork `upamanyus/bbolt` at `eb2b2e0`; the issue's test link
  (`db_whitebox_test.go#L116-L159`) checked on GitHub: the test's doc comment to its closing brace. Not filed.

## Commands and results (go1.26.9 linux/amd64)

- At `a6fa226cf` (tests only): `go test -run TestTx_Commit_MetaWriteError -count=1 .` fails:
  `expected: "v1"`, `actual  : "v3"`. Also with `FreelistType: FreelistMapType` (temporary edit in a copy).
- At `e252fc804` (fix): the test passes (both freelist types); `go test -count=1 . ./internal/... ./cmd/...`: all
  `ok` (root package 409 s). `tests/failpoint` with gofail enabled (in a copy named `bbolt`,
  `go tool go.etcd.io/gofail enable .`; `BBOLT_VERIFY=all TEST_FREELIST_TYPE={hashmap,array} go test ./tests/failpoint`):
  `ok` for both. `gofmt -l .`: nothing. `golangci-lint` v2.10.1 (the CI's) `run .`: 0 issues.
  `go vet .` reports `db_test.go:1507` (copies a lock), also at the base.
- Rerun 2026-10-21 (review pass, commits unchanged): the test fails at `a6fa226cf` with the array and the
  hashmap freelist (`expected: "v1"`, `actual  : "v3"`), passes at `e252fc804`; `TEST_FREELIST_TYPE=hashmap go
  test -count=1 . ./internal/... ./cmd/...`: all `ok` (root package 378 s); `tests/failpoint` with gofail, both
  freelist types: `ok`; `gofmt -l .`: nothing; `golangci-lint` v2.10.1 `run .`: 0 issues; `go vet .`: only
  `db_test.go:1507`, as at the base.
- Rerun 2026-10-23 (upstream `main` still a4ef197, so no rebase; commits unchanged): at `a6fa226cf`, in a copy
  (`git archive`), `go test -run TestTx_Commit_MetaWriteError -count=1 .` fails, `expected: "v1"`, `actual  :
  "v3"` (also with `TEST_FREELIST_TYPE=hashmap`); at `e252fc804` it passes (both freelist types); `go test
  -count=1 . ./internal/... ./cmd/...`: all `ok` (root package 426 s); `gofmt -l .`: nothing; `go vet .`: only
  `db_test.go:1507`. Not rerun: `tests/failpoint` and `golangci-lint` (unchanged code since the 2026-10-21 run).
- Revised 2026-10-23 after the user's review: the example read `k` only once, after the failed and the later
  commit, and a read transaction that has observed nothing before then can be linearized after the `v3` commit,
  so `v3` was not visibly wrong. The test now reads `k` in the read transaction before the failed commit (`v1`,
  a setup check) and again after the `v3` commit, each time through `rtx.Bucket` (a bucket handle cached across
  the commits keeps pointing at memory that is not reused and reads `v1` even at the base, so it does not show
  the bug): one transaction reading `v1` and then `v3` has no snapshot. Commits rebuilt (earlier `a6fa226cf`,
  `e252fc804`; never pushed): at `406c281` the test fails at the second read (`db_whitebox_test.go:158`,
  `expected: "v1"`, `actual  : "v3"`), with `TEST_FREELIST_TYPE=array` and `hashmap`; at `eb2b2e0` it passes,
  `-count=20`, both freelist types. `gofmt -l .`: nothing; `go vet .`: only `db_test.go:1507`. The fix commit is
  unchanged. Not rerun: the full suites (only the test changed).
- The panic path (not in the branch, a temporary test in a copy): `beforeSyncMetaPage` set to `panic("boom")`
  inside `db.Update`, recovered, then one more `Update`: the open reader reads `v3` at the base, `v1` with the fix.
  `Update`'s deferred `rollback` is the same code, so the fix in `rollback` covers it; a fix in `Commit` would not.

## check.py

`python3 -I .claude/skills/upstream-report/check.py bbolt-commit-meta-error-frees-reader-pages`: no FAIL. WARNs
kept: the fix's comment (it says why the early return is right, which the code does not); the issue's 266
words (the five steps are needed); the PR's 105 words (about 35 of them the fixed sentences).

## Duplicates (2026-10-21, rechecked 2026-10-23: `rollback reader pages`, `commit error created:>2026-10-20`, nothing new; repo:etcd-io/bbolt, issues and PRs)

Searched `writeMeta rollback`, `fdatasync error commit`, `rollback freelist reload`, `commit error pending pages`,
`fsync failure rollback`, `commit failed meta`, `fsync error`, `freelist rollback reader`, `writeMeta`: nothing
on this bug. Related, different: #262 (a fault in `rollback`'s `db.meta` during a remap), #152/#153 (rollback
panic with `NoFreelistSync`), #331 (a crash between the data pages' sync and the meta's), #447 (removing panics).

## Why the fix works

`beginRWTx` copies the current meta and increments its txid, so the transaction's meta has a txid one above the
current meta's until its meta page is written. The base, on a meta write error: (1) the meta bytes are in the
file, so the mapping's meta for this txid validates and `db.meta()` returns it; (2) `rollback` calls
`freelist.Rollback(txid)`, which drops `pending[txid]` (the pages the transaction freed: the old leaf and the
old freelist page, which the open reader still sees) and its allocations; (3) `Reload` reads the new freelist
page (every free and pending id at commit, the dropped ones included) and filters out only the ids still pending,
so the dropped ids become free; (4) the next writer allocates them and overwrites the reader's pages. The fix:
when `db.meta().Txid() == tx.meta.Txid()`, the in-memory freelist already matches the current meta (it is what
the successful `Commit` path keeps: `pending[txid]` released once no reader older than txid is open), so
`rollback` only closes the transaction. The `tx.db.data != nil` guard keeps `db.meta()` off an unmapped
mapping (a failed remap, the case the existing comment names); the meta cannot be the transaction's then.

## Why the test shows the bug and not a misuse

Every call is ordinary API use: `Update`, `Begin(false)`, `Get` on the open read transaction, `Commit` returning
an error that the caller handles by carrying on (bbolt rolls back on a `Commit` error precisely so that the `DB`
stays usable: `rollback`'s comment, `TestTx_Rollback_Freelist`, `TestFailpoint_LackOfDiskSpace`). The injected
error is the documented test hook `db.ops.writeAt` (added for write-failure tests, e9b2cab, 2014), made to fail
after the meta page's bytes were written, which is what an `fdatasync` failure after the write does, and what
`os.File.WriteAt` returns when a later `pwrite` of the page fails after the first part (with the meta's fields
and checksum) landed. `InitialMmapSize` avoids the remap deadlock `Begin`'s doc warns of with a reader open.
The test asserts only the guarantee: the open reader's value is unchanged.

## If a reviewer asks

Candidate layers and fixes, and why `rollback` is the one:

1. **`rollback` (chosen).** Its comment says it reloads the free pages from disk for a system error such as an
   fsync error, and an fsync error on the meta page is exactly where it does not: it drops the transaction's
   pending pages although the current meta (the one on disk and in the mapping) is the transaction's. Fixing it
   there covers every caller: `Commit`'s meta write error and `Update`'s deferred rollback after a
   panic in the same window (checked above). Six lines, no API change.
2. **`Commit`'s meta write error path** (call `close` instead of `rollback` when the meta is current): the same
   effect for the error, but misses the panic path, and leaves `rollback` wrong for its stated purpose.
3. **Reload from the freelist of the meta the transaction started from**: wrong. The new meta stays current,
   so the next writer starts from the new tree, and the old freelist lists as free the pages the new tree was
   written to: the current tree itself would be overwritten.
4. **Undo the meta write** (write the old meta back, or invalidate the new one): the mapping is read-only, a
   second write can fail like the first, and after an `fdatasync` error the page cache's contents are not
   reliable either way. Not attempted.
5. **Mark the `DB` failed after a meta write error** (refuse further transactions until reopened; the
   PostgreSQL "fsyncgate" lesson that an fsync error leaves durability unknown): bbolt has no failed state, and
   its error handling in `Commit` is designed to recover in place (the reload after an fsync error, the
   failpoint tests that keep using the `DB` after an error). A new failed state is an API change for the
   maintainers to decide, independent of this bug: even with it, the open readers must keep their pages. Worth
   raising only if a reviewer brings it up.
6. **Keep the pending pages but still roll back the allocations**: wrong for the same reason as 3: the
   allocations are the current tree's pages.

What the early return leaves, checked against the successful path (review, 2026-10-21):

- **Freelist**: exactly what a successful `Commit` leaves (`pending[txid]` and the transaction's allocations, no
  reload), so the in-memory freelist matches the current meta's freelist page; the next `beginRWTx` releases
  `pending[txid]` once no reader older than txid is open, as after a success.
- **Meta and mapping**: `db.meta0`/`db.meta1` point into the mapping, which already shows the new meta; the next
  readers and writers start from it, as after a success. `close` clears `db.rwtx`, unlocks `rwlock` and merges
  the stats; only the write count and write time of the failed meta write are not added.
- **Commit handlers** (`OnCommit`) do not run: their doc says they run after the transaction successfully
  commits, and `Commit` returns an error, so the caller is told it did not succeed; running them would
  contradict the error. Unchanged from the base.
- **Other callers of `rollback`** (`Commit`'s error paths before `writeMeta`, `Update`'s deferred rollback
  after a panic in `fn`, `commitFreelist`, the `lackOfDiskSpace` failpoint): the current meta's txid is the
  transaction's minus one (`beginRWTx` copies it and increments), so the check is false and the old path runs.
  `Rollback` by the user goes through `nonPhysicalRollback`, untouched.
- **A torn meta write** whose meta fails validation (checksum): `db.meta()` falls back to the old meta, the check
  is false and the old path runs, which is then right (temporary test in a copy: `writeAt` writes the meta
  page's first 60 bytes, then fails; the open reader keeps `v1`, a new reader sees `v3`, `tx.Check` passes).
- **Txid equality vs. pointer or a flag**: `tx.meta` is a copy, so only the txid can identify it; a "meta
  written" flag set in `Commit` would be wrong for the torn case (the file's meta is the old one) and would not
  say what readers see. `db.meta()` is exactly the meta the next transactions start from.
- **`NoFreelistSync`**: the base has the same bug there (`NoSyncReload(freepages())` scans the new tree, which
  no longer references the reader's pages); the fix covers it (temporary test in a copy with
  `NoFreelistSync: true`: fails at the tests commit, passes at the fix). Not a separate test: same symptom, same
  fix.
- **After the failed commit, with the fix**: `tx.Check` passes, and after closing the reader and reopening the
  `DB` a new reader sees `v3` and `Check` passes (temporary test in a copy, both freelist types).
- **The test's place**: `tests/failpoint` (gofail, run in CI by `failpoint_test.yaml`) has no failpoint after the
  meta page's write that returns an error (`beforeSyncMetaPage` is `struct{}`, usable only to panic or sleep),
  and adding one would put production code in the tests commit. The whitebox test uses the existing
  `db.ops.writeAt` hook and runs in the unit-test CI (`make test`). `InitialMmapSize` is needed: without it the
  test deadlocks on a remap waiting for the open reader.

The finding's second consequence (`Commit` returns an error, yet new transactions see its writes) is the same
event, not the same defect: once the meta page reached the file, the outcome is genuinely unknown (it may or may
not survive a crash), and returning an error is the honest answer; no code change can make it "not taken
effect" (alternative 4). It is asked as a documentation question in the issue's "Anything else", not split into
its own issue.

Durability after the error is out of scope: the data pages were synced before the meta page, so a later commit's
meta refers only to synced pages; a crash may lose the failed transaction's meta, which the error allows.

Backports: `rollback` is the same on `release-1.3`, `release-1.4` and `release-1.5` (the drop-then-reload dates from 4db9964, 2014); the
maintainers decide on `release-1.3`/`release-1.4` backports, with the changelog entries they add.
