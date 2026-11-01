---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/raft#441 pr merged: related, not this bug: EnsureSnapshot/EnsureSnapshotMetadata no longer reassign non-nil fields, after a race found in etcd-io/etcd#21778 (ApplySnapshot writing its argument)
blocks-proof: no
---

# raft: data race between `MemoryStorage.InitialState` and `MemoryStorage.SetHardState`

`MemoryStorage.InitialState` reads the stored hard state and `ConfState`, and may set that
`ConfState`'s `AutoLeave`, without taking the storage's mutex, so it races with `SetHardState`,
`ApplySnapshot` and `CreateSnapshot` called on another goroutine; the race detector reports it on
every run.

**Expected:** `InitialState` should be safe to call concurrently with the other methods, as
[`MemoryStorage`'s mutex comment](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/storage.go#L105-L108)
says it "protects access to all fields" and that its methods run on different goroutines.

**Impact:** an application that creates a node on a `MemoryStorage` (raft calls `InitialState` once,
in `newRaft`), or calls `InitialState` itself, while another goroutine writes to the same storage.
Raft alone does not race, and etcd does not: it fills its `MemoryStorage` before starting the node
on it. Same code in v3.7.0; release-3.6 also reads without the lock.

**Reproduction:** `TestStorageInitialStateConcurrent` in
[`issues/raft-memorystorage-initialstate-unlocked/initialstate_concurrent_test.go`](raft-memorystorage-initialstate-unlocked/initialstate_concurrent_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64:

```
$ go test -race . -run '^TestStorageInitialStateConcurrent$' -count=1
WARNING: DATA RACE
Write at 0x00c000140248 by goroutine 10:
  go.etcd.io/raft/v3.(*MemoryStorage).SetHardState()
      storage.go:140 +0x92
...
Previous read at 0x00c0000dc0c8 by goroutine 9:
  go.etcd.io/raft/v3.(*MemoryStorage).InitialState()
      storage.go:133 +0x431
...
--- FAIL: TestStorageInitialStateConcurrent (0.00s)
    testing.go:1867: race detected during execution of test
FAIL
```

**Cause:** every exported method of `MemoryStorage` takes its mutex except
[`InitialState`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/storage.go#L128-L134),
which increments a call counter, reads `ms.hardState` and the snapshot's `ConfState`, and calls
`pb.EnsureConfState` on the stored `ConfState`, all unlocked.

## Proof

no: `MemoryStorage.InitialState.spec` takes the storage's unlocked half (`memStorMeta`,
`Proof/go_etcd_io/raft/v3/InvMemstorage.lean`), which the writers need too, so it cannot run
concurrently with them (`Spec/go_etcd_io/raft/v3/MemoryStorage__InitialState.lean`); raft and etcd
meet that (one call, in `newRaft`, before any concurrent use).

## Fix

**Branch**: `fix/raft-memorystorage-initialstate-unlocked` in `~/etcd-fixes/raft-memorystorage-initialstate-unlocked` (upamanyus/etcd-raft, not pushed): ecb890e test, 15190e3 fix
**Base**: etcd-io/raft@1931ff5beacc1e2539003c0c70f096285f04c425

**PR draft**:

Title: raft: take the lock in MemoryStorage.InitialState

`MemoryStorage` embeds a mutex that, as [its comment says](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/storage.go#L105-L108), protects access to all of its fields, and every other method takes it. [`InitialState`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/storage.go#L128-L134) does not: it increments a call counter, reads the hard state and the snapshot's `ConfState`, and may set the `ConfState`'s `AutoLeave`, all without the lock, so it races with `SetHardState`, `ApplySnapshot` and `CreateSnapshot`. This PR takes the lock in `InitialState`.

The first commit adds a test of the issue's example, which fails on `main` under `go test -race`; the second, the fix, makes it pass.

A reviewer may ask about returning copies: not needed, as `MemoryStorage` never mutates in place an
object it has handed out (a `-race` stress test reading and marshalling the returned values found
nothing with the fix). The test fails only under `-race`, which raft's amd64 CI job uses. No
changelog entry (a race fix to backport, as #441).
