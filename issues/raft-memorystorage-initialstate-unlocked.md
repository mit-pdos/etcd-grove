---
upstream: known
checked: 2026-11-02
links:
  - etcd-io/raft#545 issue open: this bug (filed 2026-10-29 by NopeCharon), with the aliasing of the returned HardState and ConfState
  - etcd-io/raft#547 pr open: the fix of #545: takes the lock in InitialState and returns clones; needs-ok-to-test
  - etcd-io/raft#441 pr merged: related, not this bug: EnsureSnapshot/EnsureSnapshotMetadata no longer reassign non-nil fields, after a race found in etcd-io/etcd#21778 (ApplySnapshot writing its argument)
blocks-proof: no
---

# raft: data race between `MemoryStorage.InitialState` and `MemoryStorage.SetHardState`

`MemoryStorage.InitialState` reads the stored hard state and `ConfState`, and may set that
`ConfState`'s `AutoLeave`, without taking the storage's mutex, so it races with `SetHardState`,
`ApplySnapshot` and `CreateSnapshot` called on another goroutine; the race detector reports it on
every run.

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

## Proof

no: `MemoryStorage.InitialState.spec` is stated only for a storage not yet shared (`memStorFresh`,
`Proof/go_etcd_io/raft/v3/InvMemstorage.lean`; `Spec/go_etcd_io/raft/v3/MemoryStorage__InitialState.lean`):
it cannot run concurrently with the writers, and raft and etcd meet that (one call, in `newRaft`,
before any concurrent use).

## Notes

Raft's own goroutine is a writer too: `MemoryStorage.Snapshot`, reached from `maybeSendSnapshot`,
writes `ms.snapshot` under the lock, so an application that reads its hard state back through
`InitialState` while its node runs races with raft itself. This repository's `examples/kvdurable`
did so until 2026-10-31 (its `encode`; `go test -race -run TestRounds` reported it), and now keeps
its own copy of the hard state it last set. Our fix branch
`fix/raft-memorystorage-initialstate-unlocked` (upamanyus/etcd-raft, not pushed: ecb890e test,
15190e3 fix, on etcd-io/raft@1931ff5beacc) only takes the lock; #547 also returns clones, so ours
need not be filed.
