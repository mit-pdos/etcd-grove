---
upstream: none
checked: 2026-11-11
links:
  - etcd-io/bbolt#778 issue open: "failed to get all reachable pages" after a process restart; the same signature, no cause found; not claimed to be this bug
  - etcd-io/bbolt#701 issue closed: page corruption after power-off; not claimed to be this bug
  - etcd-io/bbolt#562 issue closed: corruption after a hard reset, attributed to ext4 fast_commit; not claimed to be this bug
blocks-proof: yes
---

# bbolt: a power loss after a process crash and a restart can corrupt the database

If the process is killed (kill -9, an OOM kill, a panic) after a commit wrote its meta page but
before that page was synced, and the database is reopened without a reboot, `Open` reads the
unsynced meta page from the OS page cache and never syncs it. The next commits reuse pages that
only the previous, durable meta page still references. A power loss before the reopened database's
first commit has synced then brings back the previous meta page over those overwritten pages: the
database no longer opens, or `Check` reports a corrupted tree or freelist.

**Expected:** a database that survives a process crash and a restart should survive a later power
loss the same way, as bbolt does for a power loss alone: the README's description of `Tx.Commit()`
("This two phase write ensures that partially written data pages are ignored in the event of a
crash",
[README.md#L947-L954](https://github.com/etcd-io/bbolt/blob/622eada16b5e733bc3bcacf17ca394452fc621f0/README.md#L947-L954)).

**Impact:** any writable database reopened after the process died during a commit, with the
default `NoSync = false`: etcd's backend (`bolt.Open` in `storage/backend/backend.go`, with
`InitialMmapSize`, the map freelist and syncs on) after a member crash or OOM kill and a restart
by its supervisor, followed by a power loss or kernel panic within the restarted process's first
commit. The window is narrow (one commit after the restart), but the outcome is a lost database,
not a lost commit. Every release; upstream `main` has the same `Open`.

**Reproduction:** `TestBoltKillThenPower` in
[`issues/bbolt-open-unsynced-meta-kill-then-power-loss/boltcrash/bolt_test.go`](bbolt-open-unsynced-meta-kill-then-power-loss/boltcrash/bolt_test.go),
a module of its own (`go.mod`, whose `replace` points at a checkout of
etcd-io/bbolt@622eada16b5e733bc3bcacf17ca394452fc621f0 (2026-11-11)) with the ptrace crash
recorder it uses (`crashsim/`), go1.27.1 linux/amd64. A child process commits random transactions
with etcd's options under ptrace; it is killed at the entry of a random `fsync`/`fdatasync` (the
page cache survives, the process does not), a second child reopens the database in place and
commits, and power-loss images are built from the two children's writes over the first one's
synced state (the POSIX `fsync` contract, and ext4/xfs-style journal ordering). Each image must
open, pass `Tx.Check`, and hold one of the states a crash may leave:

```
$ go test ./boltcrash -run TestBoltKillThenPower -count=1 -args -chains 30 -images 40
--- FAIL: TestBoltKillThenPower (76.58s)
    bolt_test.go:407: VIOLATION open/check error: panic: invalid freelist page: 8392846460364223332, p... : run 5 seed 1005 killAt 7 (inc1 commits 3, inc2 saw F) posix@K=91/seed=6818122461692326031 j=0
    bolt_test.go:407: VIOLATION open/check error: check: page 44: multiple references (stack: [43]); p... : run 5 seed 1005 killAt 7 (inc1 commits 3, inc2 saw F) ordered@K=83/seed=4695855564159389840 j=0
    bolt_test.go:407: VIOLATION open/check error: hang: reading the image did not finish in 20s (a cyc... : run 5 seed 1005 killAt 7 (inc1 commits 3, inc2 saw F) ordered@K=85/seed=4263410924841654110 j=0
    ...
    bolt_test.go:654: B: images 1160 ok 1148 violations 12 ...
    bolt_test.go:656: 12 of 1160 crash images violate
FAIL
FAIL	boltfix/boltcrash	76.626s
```

`inc2 saw F`: the restarted process opened the killed commit's meta; `j=0`: the power loss came
before its first commit returned. With the fix below, 0 of 1160 images violate.

**Cause:** a commit syncs its data pages, writes the meta page, then syncs it
([`tx.go#L595-L625`](https://github.com/etcd-io/bbolt/blob/622eada16b5e733bc3bcacf17ca394452fc621f0/tx.go#L595-L625));
a kill between the write and the sync leaves the new meta page only in the page cache. `Open` in
write mode
([`db.go#L178-L327`](https://github.com/etcd-io/bbolt/blob/622eada16b5e733bc3bcacf17ca394452fc621f0/db.go#L178-L327))
reads both meta pages, picks that one (the higher valid txid), and loads its freelist, which marks
free the pages the previous meta page still references; it syncs nothing. A power loss before the
next `fdatasync` keeps whichever of the new commit's pages reached the disk, together with the
previous meta page. bbolt's crash safety assumes the meta it starts from is on disk; after a
kill, it may not be.

## Proof

yes: the crash theorems of rung 3 cover kill-then-power-loss sequences (the user's decision,
`/shared/tmp/crash-rung3/scope.md`, Decisions), and need `Open` to sync before its first commit:
the fork fix on upamanyus/bbolt (branch `goose-lean-v2`: `c5a6065` the sync, `ea4cab5` its error
exit closing under the locks, as the failed transaction's does; `004c930` its test), pinned by
`etc/goose.py`'s project `bbolt` at `ea4cab5`. bbolt's proof of `Open` covers the sync
(`Proof/go_etcd_io/bbolt/Open.lean`, over `fdatasync.spec`); `Open`'s spec is unchanged, since
in-process durability is out of its scope. No current theorem covers bbolt crashes.

## Fix

**Fork**: upamanyus/bbolt `goose-lean-v2` at
[`ea4cab5`](https://github.com/upamanyus/bbolt/commit/ea4cab5267973cc858b7393c5c010eee4014e75c)
(`c5a6065` the sync, `ea4cab5` `db.Close()` on its failure; test `004c930`), the pin of
`etc/goose.py`'s project `bbolt`. On it, 0 of 4160 images violate (`-chains 105`). bbolt's tests
pass except the mlock tests, which this sandbox cannot run. The failpoint tests need a gofail
build and were not run.

**Branch**: `fix/bbolt-open-unsynced-meta-kill-then-power-loss` in `/shared/tmp/bbolt-fix/upstream-fix` (a worktree of a clone of etcd-io/bbolt; not pushed): afcbf6b test, 619d7de fix
**Base**: etcd-io/bbolt@622eada16b5e733bc3bcacf17ca394452fc621f0

**PR draft**:

Title: db: sync the file in Open before the first commit

A commit writes its meta page and then syncs it
([tx.go](https://github.com/etcd-io/bbolt/blob/622eada16b5e733bc3bcacf17ca394452fc621f0/tx.go#L595-L625)).
If the process dies in between, the meta page is only in the page cache, and a restarted process's
`Open` reads it without syncing. Later commits may then overwrite pages that only the previous meta
page references, and a power loss before the next sync brings that meta page back over them.

This PR makes `Open` fdatasync the file once for a writable database, unless `NoSync` is set,
before any transaction can begin (and before the freelist-sync commit `Open` itself may make). It
adds a robustness test (dm-flakey): kill bbolt at `beforeSyncMetaPage`, reopen, power-fail, and
check that the reopened state survived.

**If a reviewer asks**: Why not sync only when the meta came from the page cache? bbolt cannot
tell; one `fdatasync` per `Open` is cheap (nothing is dirty after a clean shutdown). Why not in
`Begin(true)`? `Open` is the one point every writer passes before its first commit, and syncing
there keeps commits unchanged. `NoSync` databases make no durability promise, so they skip it, as
`Commit` does.

## Notes

- The robustness test (`robustness-test.patch`, the branch's first commit: `tests/robustness/
  kill_then_powerfailure_test.go`) needs root and device-mapper and was **not run** here (no
  device-mapper in this sandbox); it compiles and vets. It checks the durability of the state the
  reopened database saw, deterministic without the fix (the meta page is still dirty when the
  device starts dropping writes), not the corruption itself, which needs a crash in the middle of
  the reopened database's first sync: the ptrace test above shows that.
- One image of the run above (`run 27 ... inc2 saw L`, "page 199: unreachable unfreed") violates
  with the restart having opened the *previous* commit: it relies on other unsynced writes of the
  killed process (its data pages or file growth). The fix covers it too (after `Open`'s sync the
  disk holds what the restarted process reads), and it did not recur with the fix.
- `fix.patch` is the fix commit's diff of `db.go`.
