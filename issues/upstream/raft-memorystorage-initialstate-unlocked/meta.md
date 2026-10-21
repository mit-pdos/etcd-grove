# raft-memorystorage-initialstate-unlocked

## Security

Not a security report: a data race inside `MemoryStorage` when the application calls `InitialState` concurrently
with a writer; no client request reaches it (raft calls `InitialState` once, in `newRaft`).

## Candidate

- **Finding**: `issues/raft-memorystorage-initialstate-unlocked.md`
- **Target**: etcd-io/raft, `main` (the same code in release-3.7; release-3.6 also takes no lock in
  `InitialState`, which there only reads)
- **Branch**: `fix/raft-memorystorage-initialstate-unlocked` in `~/etcd-fixes/raft-memorystorage-initialstate-unlocked`,
  two commits: 140bcca adds the test, which fails there under `-race`; 7ee97a9 is the fix.
- **Base**: upstream `main` 1931ff5beacc1e2539003c0c70f096285f04c425 (2026-10-21, the merge of #536)
- **State**: draft (not pushed, not filed).
- **Changelog**: none. A race fix in a stable release's code, like etcd-io/raft#441 (the analogous
  `EnsureSnapshot` race, cherry-picked to release-3.7 as #442), which the maintainers will backport; per the
  etcd-io/raft#536 review, such fixes get no changelog entry unless a reviewer asks.
- **Push** (for the issue's links): `git -C ~/etcd-fixes/raft-memorystorage-initialstate-unlocked push origin
  fix/raft-memorystorage-initialstate-unlocked`

## Duplicates checked (2026-10-21)

GitHub search, etcd-io/raft issues and PRs: `MemoryStorage InitialState` (only #431/#432, the pointer migrations,
closed), `InitialState race` (none), `MemoryStorage race` (only #435, the protoc-gen-go switch); etcd-io/etcd issues
and PRs: `MemoryStorage InitialState` (#14533, protobuf cleanup, unrelated), `InitialState race` (#21662, unrelated).
No open raft PR touches `InitialState` (the list of open PRs, 2026-10-21). Related, not this bug:
etcd-io/raft#441 (merged), after fuweid's review of etcd-io/etcd#21778 reported a race in `ApplySnapshot`'s
`EnsureSnapshot` writing the caller's snapshot.

## Why the fix works

At the base, `InitialState` (storage.go:128-134) does `callStats.initialState++`, reads `ms.hardState` and
`ms.snapshot.Metadata.ConfState`, and calls `pb.EnsureConfState`, which sets `AutoLeave` on the stored `ConfState`
when it is nil, all without `ms.Mutex`. `SetHardState`, `ApplySnapshot` and `CreateSnapshot` write those fields
under the mutex; `Snapshot` runs `EnsureSnapshot` (which may write the same `AutoLeave`) under it. The test's two
goroutines have no happens-before edge between `SetHardState`'s write of `ms.hardState` and `InitialState`'s read,
so the race detector reports it on every run (20/20). With the lock, the two calls are ordered by the mutex.

Why it is not misuse: `MemoryStorage`'s comment says the mutex protects all fields and that methods run on
different goroutines (`Append` on an application goroutine); nothing says `InitialState` is exempt. raft itself
calls `InitialState` only in `newRaft`, so raft alone does not race; the race needs the application to use the
storage from another goroutine meanwhile (creating a node while persisting, or calling `InitialState` itself).

## If a reviewer asks

Candidate layers and fixes:

1. **Take the lock in `InitialState`** (chosen). The defect is that one method skips the mutex its type documents
   as protecting all fields; every other method takes it, so this matches the file's style and fixes the reads,
   the counter and the `EnsureConfState` write at once. No caller holds the lock when calling `InitialState`
   (`newRaft` calls it through the `Storage` interface; no other caller in the module), so no deadlock.
2. **Also return copies** (`proto.Clone` of the hard state and the `ConfState`, as `Snapshot` and `CreateSnapshot`
   clone the snapshot). Not needed for this race: after `InitialState` returns, `MemoryStorage` never mutates the
   objects it handed out. `SetHardState` replaces the pointer (and stores the caller's object uncloned, so the hard
   state is shared by design); `CreateSnapshot` and `ApplySnapshot` replace `ConfState` by a fresh clone; and the
   `AutoLeave` write of `EnsureConfState` happens at most once per stored `ConfState`, now under the lock and before
   it is shared (later calls find `AutoLeave` non-nil, as #441 relies on). Cloning would add allocations and change
   aliasing behavior for no reported race; a follow-up if maintainers want `Snapshot`-style isolation.
3. **Stop `InitialState` writing** (ensure a local copy instead of the stored `ConfState`, #441's style of not
   reassigning). Still needs the lock for the `hardState` read and the counter, so it cannot replace (1); with
   the lock, the write is harmless. #441 changed `Ensure*` because `ApplySnapshot` wrote the *caller's* object, which
   no storage lock protects; here the object written is the storage's own.
4. **Document that `InitialState` must not run concurrently with writers.** Contradicts the type's comment and the
   other methods; rejected.

The simplest alternative (1) was tried first and works; nothing else was needed.

## Verification (go1.26.9 linux/amd64, 2026-10-21)

- Tests commit 140bcca: `go test -race -count=1 -run TestStorageInitialStateConcurrent .` FAIL ("race detected
  during execution of test"; write in `SetHardState` storage.go:140, read in `InitialState` storage.go:133); a
  `-race` test binary run 20 times: 20 failures. Without `-race` it passes (the test asserts only through the race
  detector; raft's `scripts/test.sh` runs with `--race` by default).
- Fix commit 7ee97a9: the test passes (20/20 runs); `go test -race -count=1 ./...` ok (raft, confchange, quorum,
  raftpb, rafttest, tracker); `gofmt -l .` empty; `go vet ./...` clean.

## Review

By hand: the only change is the lock; every caller of `InitialState` (only `newRaft`) checked; no comment or doc
claims `InitialState` runs unlocked. Side observation, not checked for reachability and not recorded as a finding:
`ApplySnapshot` still calls `pb.EnsureSnapshot` on the caller's snapshot before cloning it, so it sets the
caller's `ConfState.AutoLeave` when nil (fuweid's "clone first" follow-up on etcd-io/etcd#21778, which #441 handled
only for nil `Metadata`/`ConfState`); snapshots raft produces carry a non-nil `AutoLeave`.
