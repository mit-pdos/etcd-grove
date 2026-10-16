# etcd-io/raft#119: panic at commit 10,001

<https://github.com/etcd-io/raft/issues/119>. Filed 2023-12-18, closed 2024-01-16, no label, no fix.
The reporter's application, built on raftexample, used `go.etcd.io/etcd/raft/v3 v3.5.10`.

**The report.** After a long run (the reporter noticed commit 10,001), nodes panic with a nil
pointer dereference. The stack trace in the comments is entirely in the application:
`src/raft.(*RaftNode).GetStatus` (`return rc.node.Status().SoftState.RaftState.String()`) called
from the application's `App.Start` while the node is being set up. The maintainer (ahrtr): "not a
raft issue, nor etcd's issue ... most likely `rc.node` is nil or an invalid pointer", e.g. a race
with starting or stopping the node.

## Classification

**N** (not a bug in raft or etcd: an application race on its own `rc.node` field). The decisive
fact: the faulting frame is the application's `GetStatus`, reading `rc.node` before the goroutine
that creates it (the application's `raft.New`, started with `go`) has set it, or after it was
stopped; no raft function is on the stack. The "commit 10,001" was a coincidence of when the
application read the field. (In v3.5.10, `Status().SoftState` is a value, not a pointer, so the nil
can only be `rc.node` itself.)

## The code path

Only the application's code (`RaftNode.GetStatus`, `App.Start`), which is not etcd's or raft's.
The raft API it would have reached, `node.Status` (`node.go`), is in the raft pin but only
translated (`verified.txt`: `node.Status` and `RawNode.Status` translated, `RawNode.BasicStatus`
verified); in any case the fault is before raft is called. No spec here is involved: the
behavior is outside every package this repository translates (O-pkg if one insists on a class for
the code; N because there is no bug in the Go code verified or translated here).

## Proposal

None (class N).

## Files

None besides this report.
