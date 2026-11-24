---
upstream: none
checked: 2026-11-24
links:
  - etcd-io/raft#558 issue open: related, not this bug: a crash between a Ready's entries and its HardState during a joint change elects a leader in a stale configuration
  - etcd-io/raft#561 pr open: related, not this bug: scans the whole log for unapplied conf changes before campaigning; by its description it does not block this campaign (the node has applied every conf change it holds; not tested)
  - etcd-io/raft#553 pr open: related, not this bug: rejects Bootstrap on a storage with a persisted HardState
blocks-proof: no
---
# raft: with a small `MaxSizePerMsg`, a node that crashes while persisting its bootstrap `Ready` can elect itself in part of the initial configuration

A node started with `StartNode` (or `RawNode.Bootstrap`) whose first `Ready` is interrupted after
some of its entries are written and before its `HardState` is restarts with no configuration and
commit index 0. When the leader then sends it the rest of the bootstrap log one entry per append
(a small `MaxSizePerMsg`), the node learns that a prefix of the bootstrap conf changes is committed,
applies it, and is a voter of that prefix's configuration, which a minority of the initial voters
forms. Cut off from the leader, it wins an election there and commits a different entry at an
index the cluster committed at bootstrap. With voters 1, 2, 3, `MaxSizePerMsg` 1, nodes 1 and 2
keeping only index 1 of their bootstrap `Ready`: node 3 leads, node 1 learns that index 2 is
committed (voters 1, 2), then nodes 1 and 2 are partitioned from node 3, node 1 wins term 3 with
node 2's vote and commits its empty entry at index 3, where the bootstrap put the conf change adding
voter 3.

**Expected:** an index should never be committed with two different entries, whatever point a
crash interrupts the application at; if raft relies on a `Ready`'s entries and `HardState` being
written atomically, [doc.go's step 1](https://github.com/etcd-io/raft/blob/ae830f4a15a0bdb5f59bb7988e50663e92cc028f/doc.go#L75-L77)
should say so, and if `Bootstrap` relies on `MaxSizePerMsg` covering its entries,
[its documentation](https://github.com/etcd-io/raft/blob/ae830f4a15a0bdb5f59bb7988e50663e92cc028f/raft.go#L189-L193)
should say so.

**Impact:** an application that bootstraps a cluster with `StartNode`, uses a `MaxSizePerMsg`
smaller than the bootstrap log (0, "at most one entry per message", or a few bytes), and crashes in
the middle of persisting a node's first `Ready`; at least two nodes must lose their bootstrap
`HardState` for the self-election to find a quorum (in the test, nodes 1 and 2). PreVote and
CheckQuorum do not prevent it: the test uses them. etcd is not affected in its configuration: its
`MaxSizePerMsg` is 1 MiB (`server/etcdserver/raft.go`), so an append carries the whole bootstrap
log and the node commits all of it at once (`TestBootstrapTornFirstReady` and
`TestBootstrapTornAnyReady` below, with etcd's settings, pass). Present in v3.7.0 and `main`.

**Reproduction:** `TestRestartWithPartOfBootstrapEntries` in
[`issues/raft-bootstrap-entries-kept-small-appends/bootstrap_partial_test.go`](raft-bootstrap-entries-kept-small-appends/bootstrap_partial_test.go)
(three `RawNode`s on `MemoryStorage`s bootstrapped with `Bootstrap`, PreVote and CheckQuorum,
`MaxSizePerMsg` 1, each `Ready` handled as doc.go describes, conf changes applied before `Advance`;
nodes 1 and 2 keep the first entry of their first `Ready` and nothing else, and restart with
`NewRawNode` from their storage), copied into the module root at
etcd-io/raft@ae830f4a15a0bdb5f59bb7988e50663e92cc028f (2026-11-19), go1.27.3 linux/amd64 (also fails
at v3.7.0 and at the verified fork's d2c16c5):

```
$ go test . -run '^TestRestartWithPartOfBootstrapEntries$' -count=1
--- FAIL: TestRestartWithPartOfBootstrapEntries (0.00s)
        	Error:      	Not equal:
        	            	expected: "1/3 EntryConfChange v3"
        	            	actual  : "3/3 EntryNormal \"\""
        	Messages:   	index 3 committed on nodes 3 and 1
FAIL
```

**Cause:** `Bootstrap` appends one conf change per peer and marks them committed without any
quorum ([`bootstrap.go`](https://github.com/etcd-io/raft/blob/ae830f4a15a0bdb5f59bb7988e50663e92cc028f/bootstrap.go#L52-L80)):
that the bootstrap log is committed is an assumption every node makes about every other. A node that
lost its first `HardState` restarts with commit index 0 and the snapshot's empty `ConfState`, and a
follower commits `min(m.Commit, last new index)` of an append, so with appends of one entry it
commits the bootstrap log one entry at a time and passes through the configurations of its
prefixes; `hup` lets it campaign in one as soon as it has applied what it committed. The
configuration of a prefix is not one the cluster ever used, and its quorums need not intersect
the initial configuration's.

## Proof

no: etcd's `MaxSizePerMsg` (1 MiB) covers the bootstrap log; the raft proof's `RestartNode.spec`
restarts a node only once its stored commit covers the bootstrap log (`γ.bootLen ≤ σ.commit`), so
no proved result restarts below it; etcd's crash proof (D6, `notes/etcd-dist-d6.md`) must
restart members below it and so must use that bound (`notes/etcd-dist-d6.md`, "T1's result").

## Fix

No upstream branch. Either have `Bootstrap`'s nodes persist the bootstrap log and its commit atomically
(document it; or, as `Bootstrap`'s comment already recommends, bootstrap from a storage whose
snapshot holds the initial `ConfState`), or refuse to campaign while the node's commit index is
below the bootstrap log's last index.

etcd's side of the first is written on our fork (upamanyus/etcd branch
`goose-lean-fmtattrs-tornsave`, the fix of `raft-commit-lost-with-entries-kept.md`): a torn `Save`
reads back as none, and a member whose WAL holds nothing a `Save` wrote (a crash between `wal.Create`
and the end of its first `Save`) bootstraps again with `StartNode` instead of restarting raft on an
empty log (`TestBootstrapUnsavedWALBootstrapsFresh`, `server/etcdserver/bootstrap_unsaved_test.go`).
etcd then never restarts a member below its bootstrap commit, whatever `MaxSizePerMsg` is.

## Notes

`TestBootstrapTornFirstReady` and `TestBootstrapTornAnyReady` in
[`bootstrap_torn_test.go`](raft-bootstrap-entries-kept-small-appends/bootstrap_torn_test.go)
(randomized: 300 schedules each of ticks, message deliveries and drops, partitions, campaigns and
proposals, for 1, 3 and 5 members bootstrapped as etcd does, with etcd's `raftConfig` settings;
member 1's first `Ready` torn at a random prefix, and in the second test every member also crashing
before, after or in the middle of any later `Ready`) pass at the same commits: no index committed
twice, and member 1 a voter of the whole configuration once the network heals, unless every member
lost its bootstrap `Ready` (a single-member cluster always does: it can then never elect a leader,
a liveness loss). With `MaxSizePerMsg` 1 the same harness finds the split in a few seeds of 3000.
A crash before anything of the first `Ready` is written behaves the same when the application
restarts with `RestartNode` on the empty storage, as etcd does when its WAL exists (created before
the first `Save`); doc.go's guidance is to `StartNode` again on an empty storage.
