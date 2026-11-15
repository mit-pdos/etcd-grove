---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/raft#300 pr closed: same root cause (HardState.Commit not persisted with the entries), different symptom (force-new-cluster drops a committed entry); closed, resolved on the etcd side
  - etcd-io/raft#234 issue closed: related, not this bug: split brain with a stalled apply; closed citing hasUnappliedConfChanges (assumes conf changes applied before the applied index moves)
blocks-proof: no
---
# raft: a crash after a `Ready`'s entries are written but before its `HardState` lets two nodes commit different entries at one index

A follower that catches up on two membership changes in one `Ready` and crashes after writing the
entries but before writing the `HardState` that commits them restarts with its old configuration
and a commit index below both changes. Raft's check against campaigning with unapplied conf changes
then sees none, so the node can win an election counted in its old configuration while the rest of
the cluster has a leader in the new one, and the two commit different entries at the same index.
With voters 1, 2, 3 and node 3 leading: while node 1 is cut off, node 3 adds voters 4 and 5
(indexes 2 and 3); node 1 reconnects, receives indexes 2 and 3 with commit index 3 in one `Ready`,
writes the entries and crashes; after a partition `{1, 2} | {3, 4, 5}`, node 3 commits `y` at index
4 with nodes 4 and 5, and node 1 wins term 2 with node 2's vote (a majority of `{1, 2, 3}`) and
commits its empty entry at index 4 with node 2.

**Expected:** an index should never be committed with two different entries, whatever point a
crash interrupts the application at; if raft relies on the entries and the `HardState` of a
`Ready` being written atomically, [doc.go's step 1](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/doc.go#L75-L77)
("Write HardState, Entries, and Snapshot to persistent storage") should say so.

**Impact:** a node that lags behind two committed membership changes, receives both in one
append, crashes in the middle of persisting it, and later campaigns in a partition that splits its
old configuration's majority from the new one's. etcd's settings (PreVote, CheckQuorum) do not
prevent it: the test uses them. Whether etcd's WAL reaches the interrupted write: `WAL.Save`
encodes the entry records, then the state record, into a page writer that writes to the file when
its 128 KiB buffer fills and at the fsync that ends the `Save`
([`server/storage/wal/wal.go`](https://github.com/etcd-io/etcd/blob/main/server/storage/wal/wal.go),
`Save`; `pkg/ioutil/pagewriter.go`). A process kill during a `Save` of more than 128 KiB of
entries, after the buffer was first written out and before the state record was, leaves a prefix
of the entry records without the state record; a power loss before the fsync completes can keep
the pages holding the entries and lose the one holding the state record. On restart etcd repairs a
torn last record (`bootstrap.go`, `wal.Repair`) and builds raft's storage from the records left.
This etcd path was found by reading the code, not reproduced on a cluster. Present in v3.7.0 and
`main`.

**Reproduction:** `TestRestartWithEntriesButNotCommit` in
[`issues/raft-commit-lost-with-entries-kept/commit_lost_with_entries_kept_test.go`](raft-commit-lost-with-entries-kept/commit_lost_with_entries_kept_test.go)
(five `RawNode`s on `MemoryStorage`s with PreVote and CheckQuorum, each `Ready` handled as doc.go
describes, conf changes applied before `Advance`; node 1's crash keeps the `Ready`'s entries and
drops the rest, and it restarts with `NewRawNode` from its storage), copied into the module root at
etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64 (also fails at v3.7.0 and at the
verified fork's 565c2bda9e6d):

```
$ go test . -run '^TestRestartWithEntriesButNotCommit$' -count=1
--- FAIL: TestRestartWithEntriesButNotCommit (0.00s)
    commit_lost_with_entries_kept_test.go:152:
        	Error:      	Not equal:
        	            	expected: "1/4 EntryNormal \"y\""
        	            	actual  : "2/4 EntryNormal \"\""
        	Messages:   	index 4 committed on nodes 3 and 1
FAIL
```

**Cause:** after a restart raft's configuration is the snapshot's `ConfState`, its applied index
the snapshot's index (etcd sets no `Config.Applied`), and its commit index the stored
`HardState.Commit` ([`newRaft`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L478-L487)).
[`hup`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L983-L986)
refuses to campaign only while a conf change lies in `(applied, committed]`; conf changes the node
holds above its stored commit index are invisible to it, although the cluster has committed them
and they make the node's configuration out of date. One conf change is not enough to split the
majorities, and the leader does not accept a second one until the first is applied, so any
`MsgApp` carrying the second carries a commit index covering the first: only a `Ready` whose
entries survive and whose `HardState` does not reaches it. (Losing a later commit-only
`HardState`, which `MustSync` lets the application write without fsync, does not: the commit index
stored with the second change already covers the first.)

## Proof

no: not reached by the top-level results (no conf change is applied in the verified scope, and no
restart from a torn write); the reconfiguration work assumes the entries and `HardState` of a
`Ready` persist atomically (`notes/reconfiguration-safety.md`, A2).

## Fix

Not written. Either document that a `Ready`'s `HardState` and entries must be persisted atomically
(and make etcd's WAL recovery drop entry records not followed by the state record of their `Save`),
or make raft's guard independent of the stored commit index (refuse to campaign while any conf
change above the applied index is in the log, at the cost of a node holding an uncommitted conf
change not campaigning until it learns the commit index).

## Notes

Found first as an abstract model's execution (`notes/raft-conf-lag-model/`, `python3 model.py 4 3
crash 3 5 2 2 simple trace-crash.txt`); the Go test reaches the same split. Writing the
`HardState` before the entries does not help: `loadState` panics on a commit index past the last
entry.
