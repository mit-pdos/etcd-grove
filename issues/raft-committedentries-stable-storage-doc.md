---
upstream: unchecked
checked: 2026-10-28
links: []
---

# raft: `Ready.CommittedEntries` "have previously been appended to stable storage", which the synchronous mode contradicts

**Status**: documentation (wrong). An application that relies on it can read or snapshot an entry its
storage does not hold yet.

**Where** (etcd-io/raft v3.7.0 plus the fork's fixes, `c8217eb9`, `etc/goose.py`'s pin):

- `node.go:89-91` (`Ready.CommittedEntries`): "CommittedEntries specifies entries to be committed to a
  store/state-machine. These have previously been appended to stable storage."
- `log.go:216-219` (`raftLog.nextCommittedEnts`): "Entries can be committed even when the local raft
  instance has not durably appended them to the local raft log yet. If allowUnstable is true, committed
  entries from the unstable log may be returned".
- `rawnode.go:144`, `443-444`: without `AsyncStorageWrites` (`Config.AsyncStorageWrites = false`, etcd's
  setting) `RawNode` calls it with `allowUnstable` true, so a `Ready` may carry an entry both in `Entries`
  (to append) and in `CommittedEntries` (to apply).

**What happens**: in the synchronous mode a `Ready`'s `CommittedEntries` may include entries of the same
`Ready`'s `Entries`, which the application has not appended yet when it receives the `Ready`. An
application that takes the documentation at its word and, say, creates a snapshot at a committed index
(`MemoryStorage.CreateSnapshot`) before appending the `Ready`'s entries panics (`storage.go:250-252`,
"snapshot ... is out of bound lastindex"); the documented order of the usage steps (`doc.go`: append, then
apply) avoids it, and etcd's server waits for the append before applying (`server/etcdserver/raft.go`,
the `notifyc` hand-off before applying). The field's comment is the only statement on the `Ready` itself.

**Expected**: "In the synchronous mode, these may include entries of this `Ready`'s `Entries`: append those
first (see the usage in `doc.go`)."

**How the proof handles it**: the specs never derive "held by the storage" from "committed and delivered":
the unified node API's `CreateSnapshot` takes a storage witness given by the append receipt and by `Advance`
(`notes/raft-unified-plan.md`, U8).

**Possible fixes**: correct the comment (documentation only).

**Found**: 2026-10-28, by spec review 9 of the unified node API
(`notes/spec-first-study/raft-node-unified-review-9.md`).
