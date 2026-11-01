---
upstream: none
checked: 2026-10-28
links: []
---

# raft: a member added after the storage's latest snapshot is sent that snapshot forever

**Status**: a liveness bug at the boundary of raft and its storage, an unstated precondition
(documentation). A leader sends a follower whose next entries are compacted away its storage's
`Snapshot()` -- the `Storage` interface asks for "the most recent snapshot" -- and a follower drops
a snapshot whose configuration does not include it ("should never happen", raft's log says). A
member added after the storage's latest snapshot, once it needs entries below the storage's first
index (a newcomer always does: its log is empty), is sent that snapshot, drops it, and is sent it
again, for as long as the storage's latest snapshot predates its addition. If the configuration
needs its vote to commit (a second voter added to a one-voter cluster; a joint configuration whose
incoming half it is part of), nothing commits any more, so the application never applies anything
new to take a newer snapshot from: the cluster is stuck for good. Nothing in raft's documentation
says that a storage's snapshot must include every member the leader may send it to.

etcd is not affected: it replaces the metadata of every snapshot raft sends by its applied index
and configuration (`createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)`,
`server/etcdserver/server.go:1013`, `snapshot_merge.go:44-48`, at the fork's `goose-lean` pin of
`etc/goose.py`). An application on `MemoryStorage` that takes snapshots only every N entries
is, once its log has been compacted (`contrib/raftexample`'s pattern, not checked there: with its
defaults the newcomer of a three-voter cluster would only wait for the next snapshot, 10000 entries
later, while one added to a one-voter cluster would be stuck).

**Where** (etcd-io/raft v3.7.0 plus the fork's fixes, `c8217eb9`, `etc/goose.py`'s pin):

- `storage.go:91-95`: `Snapshot` "returns the most recent snapshot", nothing about whom it must
  include.
- `raft.go:666-681`: `maybeSendSnapshot` sends `r.raftLog.snapshot()`, the storage's.
- `raft.go:1869-1898` (`restore`): "throw away snapshot if recipient is not in the config. This
  shouldn't ever happen (at the time of writing)"; it logs "should never happen" and returns false.
  The follower answers as for any snapshot it does not take, and the leader, told the snapshot was
  delivered (`ReportSnapshot`) or after the follower's response, probes again, finds the entries
  compacted and sends the same snapshot.

**What happens**: reproduction (package `kvreconf` of this repository's examples module, raft alone:
`RawNode`, `MemoryStorage`, a lossless in-memory network, run step by step):
[examples/kvreconf/livelock_test.go](../examples/kvreconf/livelock_test.go), `cd examples/kvreconf
&& go test -run TestStaleSnapshotLivelock -v .`. A one-voter cluster applies 11 entries, takes a
snapshot at 11 and compacts its log to it, then adds voter 2 (committed alone, by the old
configuration) and proposes an entry. After 200 rounds of ticks and message delivery the newcomer
has applied nothing and the proposal is not committed (`fixSnapshot=false: snapshot at 11, leader
applied 13 -> 13, newcomer applied 0`). With a snapshot taken right after the change is applied,
the newcomer catches up and the proposal commits (`fixSnapshot=true: ... leader applied 13 -> 14,
newcomer applied 14`).

Found first in `examples/kvreconf` (a joint change whose incoming voters were newcomers: the joint
configuration never committed again, and raft's automatic leave never happened).

**Expected**: either raft's documentation says what the storage's snapshot must satisfy (that the
leader sends it to any member that needs it, and that a member drops one without itself in its
configuration), or raft does not keep sending a snapshot the recipient cannot take.

**How the proof handles it**: not at all, and it need not: it is a liveness problem, and the proofs
are of safety. The examples' stores avoid it: `examples/kvreconf`'s `Replica.run` takes a snapshot
after every configuration change it applies; `examples/kv` adds no member.

**Possible fixes**:

- Documentation: `Storage.Snapshot` (and `MemoryStorage`) say that the snapshot the leader sends must
  contain the recipient in its configuration, so the application must take a snapshot after a
  configuration change that adds a member, before that member can need one (or build the snapshot
  when asked, returning `ErrSnapshotTemporarilyUnavailable` meanwhile, as the interface allows).
- In raft: `maybeSendSnapshot` does not send a snapshot whose configuration lacks the recipient
  (it treats it as temporarily unavailable, as for `ErrSnapshotTemporarilyUnavailable`), which at
  least stops the loop of useless sends, but does not unstick the cluster by itself.

Related: [raft-compact-past-snapshot](raft-compact-past-snapshot.md) (another precondition on what
the storage's snapshot must cover; its "the leader sends it the same snapshot again" variant).

**Found**: 2026-10-28, writing the randomized test of `examples/kvreconf`.
