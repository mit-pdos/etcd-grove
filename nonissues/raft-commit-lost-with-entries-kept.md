---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/raft#300 pr closed: same root cause (HardState.Commit not persisted with the entries), different symptom (force-new-cluster drops a committed entry); closed, resolved on the etcd side
  - etcd-io/raft#234 issue closed: related, not this bug: split brain with a stalled apply; closed citing hasUnappliedConfChanges (assumes conf changes applied before the applied index moves)
blocks-proof: no
---
# raft: entries persisted without their `HardState.Commit` can let a node campaign with an unapplied conf change

raft refuses to campaign while a conf change lies in `(applied, committed]`, and after a restart
`committed` is the persisted `HardState.Commit`. If a node persists a `Ready`'s entries but crashes
before its new commit index is durable, it restarts with a configuration older than its committed
log and a commit index low enough that the guard sees no unapplied conf change; in an abstract
model this lets it win an election with an outdated configuration and commit a different entry at
an index already committed. `doc.go` (step 1 of handling a `Ready`) asks for the entries and the
`HardState` to be written, but not atomically; writing the `HardState` first does not work either
(`loadState` panics on a commit index past the last entry).

**Why not an issue:** no Go test, only an abstract model's execution (`raft-conf-lag-model/`,
`python3 model.py 4 3 crash 3 5 2 2 simple trace-crash.txt`, and the checker's
`trace-check-crash-sms.txt`); atomic persistence of a `Ready`'s entries and `HardState` is part of
the storage contract a raft specification has to state (INDEX-reviewed.md's Plan: "the raft spec
will have to cover this").

## Proof

no: not reached (no conf change is applied in the verified scope); the reconfiguration work
assumes atomic persistence in the storage's spec (`notes/reconfiguration-safety.md`).

## Notes

etcd's WAL writes the entry records, then the state record, before one fsync; whether a torn tail
after a power loss can keep the entries and drop the state was not tested. A test through the WAL
(or through `RawNode` with a storage that persists entries but not the `HardState`) could promote
this. The guard fix of `raft-conf-lag-model/guard-fix.md` does not address it.
