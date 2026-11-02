---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---
# raft: `MemoryStorage`'s mutex comment names only `Append` as the application's, but every writer is

[`MemoryStorage`'s mutex comment](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/storage.go#L105-L107)
says "Most methods of MemoryStorage are run on the raft goroutine, but Append() is run on an
application goroutine". raft calls only the `Storage` interface's read methods, on its own
goroutine; every writer (`Append`, `ApplySnapshot`, `SetHardState`, `CreateSnapshot`, `Compact`) is
the application's. In etcd, `ApplySnapshot` and `Append` run on the goroutine handling `Ready`s and
`CreateSnapshot` and `Compact` on the apply goroutine, each concurrently with raft's reads. An
implementer of another `Storage` who reads the comment as "only `Append` needs synchronization"
would leave the other writers unprotected.

**Why not an issue:** documentation only, no bug: the mutex does protect every `MemoryStorage`
method that writes (`InitialState`'s unlocked read is
[`raft-memorystorage-initialstate-unlocked`](../issues/raft-memorystorage-initialstate-unlocked.md)).

## Proof

no: the storage model is linearizable (every locked `MemoryStorage` spec takes the lock,
`Proof/go_etcd_io/raft/v3/InvMemstorage.lean`); the comment is not used.

## Notes

A doc fix: "raft calls only the `Storage` interface's methods, on its own goroutine; the writers
(`Append`, `ApplySnapshot`, `SetHardState`, `CreateSnapshot`, `Compact`) are the application's,
possibly on other goroutines, concurrently with raft's reads." Found 2026-10-28, explaining raft's
storage handshake in the unified node API's stage U4a. Upstream searched 2026-11-02 (`MemoryStorage
mutex`, issues and PRs): only etcd-io/raft#545/#547, which are the `InitialState` race.
