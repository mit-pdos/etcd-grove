# raft-memorystorage-initialstate-unlocked

## Security

Not a security report: a data race inside `MemoryStorage` when the application calls `InitialState` concurrently
with a writer; no client request reaches it (raft calls `InitialState` once, in `newRaft`).

## Candidate

- **Finding**: `issues/raft-memorystorage-initialstate-unlocked.md`
- **Target**: etcd-io/raft, `main` (the same code in release-3.7; release-3.6 also takes no lock in
  `InitialState`, which there only reads)
- **Branch**: `fix/raft-memorystorage-initialstate-unlocked` in `~/etcd-fixes/raft-memorystorage-initialstate-unlocked`,
  two commits: ecb890e `raft: test InitialState concurrent with SetHardState` adds the test, which fails there
  under `-race`; 15190e3 `raft: take the lock in MemoryStorage.InitialState` is the fix (body: "Reading the initial
  state did not hold the mutex that guards the storage.").
- **Base**: upstream `main` 1931ff5beacc1e2539003c0c70f096285f04c425 (2026-10-21, the merge of #536; still
  `main` on 2026-10-23, so the branch was not rebuilt; not pushed: `git ls-remote origin` has no such branch)
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

Re-checked 2026-10-23: etcd-io/raft `InitialState` (only #423/#431/#432, closed protobuf migrations),
`MemoryStorage race` (only #435), `MemoryStorage lock` open (none); etcd-io/etcd `InitialState race` (#21662,
unrelated). The open raft PRs (list of 2026-10-23: dependency bumps, TLA+ work, #96 memory deallocation of stable
entries, ...) do not touch `InitialState`.

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
   clone the snapshot). Not needed: with the lock, the pointers `InitialState` returns do not race with later
   storage writes, because `MemoryStorage` never mutates in place an object it has handed out. `hardState` is a
   `*pb.HardState` that `SetHardState` replaces (it stores the caller's object uncloned, so the hard state is
   shared with the application by design); `ApplySnapshot` replaces `ms.snapshot` by a clone and `CreateSnapshot`
   replaces `Metadata.ConfState` by a clone (it mutates `Metadata.Index`/`Term` in place, but `InitialState` returns
   only the `ConfState`); the stored `ConfState` is never shared before `InitialState` or `Snapshot` (which returns
   a clone) has run `EnsureConfState` on it under the lock, so the one in-place write, `AutoLeave` when nil,
   happens before any caller holds the pointer, and later `EnsureConfState` calls only read it (#441, merged as
   fe48d373, made `EnsureSnapshot`/`EnsureSnapshotMetadata` stop reassigning non-nil fields for the same reason;
   `EnsureConfState` already writes only when nil). raft's one caller, `newRaft`, only reads the returned values
   (`confchange.Restore`, `loadState`). Checked by a throwaway `-race` stress test (not on the branch, via
   `-overlay`): `CreateSnapshot` with a `ConfState` whose `AutoLeave` is nil, `Snapshot` and `SetHardState` in a
   loop against two goroutines calling `InitialState` and reading, cloning and marshalling the returned values,
   then `ApplySnapshot`: no race in 3 runs with the fix. So no test can show a pointer race, and cloning would
   add allocations and change aliasing for nothing.
3. **Stop `InitialState` writing** (ensure a local copy instead of the stored `ConfState`, #441's style of not
   reassigning). Still needs the lock for the `hardState` read and the counter, so it cannot replace (1); with
   the lock, the write is harmless. #441 changed `Ensure*` because `ApplySnapshot` wrote the *caller's* object, which
   no storage lock protects; here the object written is the storage's own.
4. **Document that `InitialState` must not run concurrently with writers.** Contradicts the type's comment and the
   other methods; rejected.

The simplest alternative (1) was tried first and works; nothing else was needed.

Other methods: every other exported method of `MemoryStorage` takes the mutex before touching a field (`Append`
checks only `len(entries)`, its argument, before locking); `lastIndex`/`firstIndex` are called under it.
`InitialState` was the only gap.

Does CI see the test? The test fails only under `-race`. raft's CI does run with it: `.github/workflows/
test_amd64.yaml` runs target `linux-amd64-unit-4-cpu-race`, which `test_template.yaml` maps to `RACE='true'
./scripts/test.sh` (`PASSES='unit'`), whose `run_unit_tests` passes `--race`; `scripts/test.sh` also defaults to
`--race` on amd64 (so `make test` does too). The 386 job runs without it, where the test passes vacuously.

## Verification (go1.26.9 linux/amd64, 2026-10-21)

- Tests commit ecb890e: `go test -race -count=1 -run TestStorageInitialStateConcurrent .` FAIL ("race detected
  during execution of test"; write in `SetHardState` storage.go:140, read in `InitialState` storage.go:133); a
  `-race` test binary run 20 times: 20 failures. Without `-race` it passes (the test asserts only through the race
  detector; raft's CI runs it with `-race`, above).
- Fix commit 15190e3: `go test -race -count=20 -run TestStorageInitialStateConcurrent .` ok; `go test -race -count=1 ./...` ok (raft, confchange, quorum,
  raftpb, rafttest, tracker); `gofmt -l .` empty; `go vet ./...` clean.
- Rerun 2026-10-23 (same toolchain, same commits): at ecb890e `go test -race -count=1 -run
  TestStorageInitialStateConcurrent .` reports the same race (write storage.go:140 in `SetHardState`, read
  storage.go:133 in `InitialState`), and the `-race` binary fails 20/20; at 15190e3 the test passes (`-count=20`),
  `go test -race -count=1 ./...` ok in all six packages, `gofmt -l .` empty, `go vet ./...` clean.
- `check.py`: one WARN, the issue names `InitialState`; kept, as it is the exported `Storage` method the
  application calls and the symptom is about. Since the issue's free-form rewrite with the cause (2026-10-23
  review), no WARN: a raft issue names the code it explains.

## Review

Revised 2026-10-21 (maintainer pass): the test's goroutine sends `SetHardState`'s error on a channel instead of
calling `require` off the test goroutine (`FailNow` must run on it), as `node_test.go` does; the doc comment
shortened; the fix commit's body in words. Fix unchanged (the lock is the whole root cause, item 2 above).

By hand: the only change is the lock; every caller of `InitialState` (only `newRaft`) checked; no comment or doc
claims `InitialState` runs unlocked. Side observation, not checked for reachability and not recorded as a finding:
`ApplySnapshot` still calls `pb.EnsureSnapshot` on the caller's snapshot before cloning it, so it sets the
caller's `ConfState.AutoLeave` when nil (fuweid's "clone first" follow-up on etcd-io/etcd#21778, which #441 handled
only for nil `Metadata`/`ConfState`); snapshots raft produces carry a non-nil `AutoLeave`.
