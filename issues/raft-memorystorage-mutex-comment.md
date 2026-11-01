---
upstream: unchecked
checked: 2026-10-28
links: []
---

# raft: `MemoryStorage`'s mutex comment names only `Append` as the application's, but every writer is

**Status**: documentation (incomplete). Not a bug: the mutex does protect every method.

**Where** (etcd-io/raft v3.7.0 plus the fork's fixes, `565c2bd`, `etc/goose.py`'s pin):

- `storage.go:105-107` (`MemoryStorage.Mutex`): "Protects access to all fields. Most methods of
  MemoryStorage are run on the raft goroutine, but Append() is run on an application goroutine."
- raft calls only the `Storage` interface's methods (`InitialState`, `Entries`, `Term`, `LastIndex`,
  `FirstIndex`, `Snapshot`), on its own goroutine. Every method that writes the storage is the
  application's: `Append` (`:293`), `ApplySnapshot` (`:218`), `SetHardState` (`:137`), `CreateSnapshot`
  (`:243`), `Compact` (`:268`).

**What happens**: the comment suggests a single writer racing with raft. In etcd's server, `ApplySnapshot`,
`SetHardState` and `Append` run on the goroutine handling `Ready`s (`server/etcdserver/raft.go`), and
`CreateSnapshot` and `Compact` on the apply goroutine (`EtcdServer.snapshot`, `compactRaftLog`): several
writers, on two goroutines, each concurrent with raft's reads. An implementer of another `Storage` who reads
the comment as "only `Append` needs synchronization" would leave the others unprotected.

**Expected**: "raft calls only the `Storage` interface's methods, on its own goroutine; the writers
(`Append`, `ApplySnapshot`, `SetHardState`, `CreateSnapshot`, `Compact`) are the application's, possibly on
other goroutines, concurrently with raft's reads."

**How the proof handles it**: the storage model is linearizable (every `MemoryStorage` spec takes the lock);
the server's `CreateSnapshot`/`Compact` run through atomic specs over the shared snapshot token
(`MemstorageAU.lean`). Raft's own proof lends the storage exclusively only while a snapshot is pending,
when raft provably reads none of it.

**Possible fixes**: correct the comment.

**Found**: 2026-10-28, explaining raft's storage handshake in the unified node API's stage U4a.
