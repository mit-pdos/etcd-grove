# etcd-io/raft#174: a 4th node cannot rejoin the raftexample cluster after compactions and leader changes

<https://github.com/etcd-io/raft/issues/174>. Closed 2024-03-04, a day after filing. The maintainer
(ahrtr) said that enabling PreVote should resolve it and that raftexample is unmaintained. No fix.

**The report.** The setup is etcd's `contrib/raftexample`, patched to snapshot and compact after
every entry. Node 4 is added with `--join` to `{1,2,3}`, then killed. The leaders are then
killed and restarted several times. Each of nodes 1–3 is restarted with the original 3-node
`--cluster` list. Restarted, node 4 never gets a snapshot or an append. It campaigns forever
(term 51 → 105), and no MsgVote is ever answered. Removing node 4 and adding it again makes the
leader send it a snapshot.

## Classification

**O-pkg** (secondary N: example code, removed upstream). The likely cause is in raftexample's
transport bookkeeping, not in raft. raftexample adds `rafthttp` peers from its `--cluster` list
(`contrib/raftexample/raft.go:323-327` at `ceb97712e^`) and from `ConfChangeAddNode` entries as
it publishes them (`:174-179`). It never adds them from a snapshot's `ConfState`. A node
restarted from a snapshot that covers node 4's `AddNode` therefore has node 4 in raft's
configuration (raft `Progress`, and the leader keeps trying `MsgApp`/`MsgSnap`) but not in its
transport. Messages to node 4 are dropped, and node 4's own messages find no known sender. That
matches the logs: one vote (its own) in every round, and the cluster's term unaffected. Removing
and re-adding node 4 goes through a `ConfChangeAddNode` entry, which re-adds the transport peer,
and that is why it "fixes" it. raftexample was deleted upstream (`ceb97712e`, "Cleanup the
legacy raftexample", an ancestor of the etcd pin `107edf7e4`), and `rafthttp` is translated
names-only (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp.toml`: `translate = ["!*"]`).

## The code path and its verification state

Source: `Code/` and the spec files directly (no `verified.txt`).

| Go function | State |
|---|---|
| `raftexample` `raftNode.startRaft`, `publishEntries`, `replayWAL` (`contrib/raftexample/raft.go`) | not translated (deleted before the pin) |
| `rafthttp.Transport.AddPeer`/`Send`, stream handlers | translated names-only (bodies axiomatized, unspecified) |
| raft: `raft.maybeSendAppend` → `maybeSendSnapshot` (leader sends a snapshot when `Next` is compacted) | verified (`Spec/go_etcd_io/raft/v3/raft__maybeSendAppend.lean`, `raft__maybeSendSnapshot.lean`) |
| raft: `RawNode.ReportUnreachable`, `ReportSnapshot` | verified |

The raft side does what it should: the leader puts the messages in `Ready.Messages`, and the
verified specs say nothing about delivery, which belongs to the application. Even with delivery,
a partial-correctness spec could not state "node 4 eventually catches up" (C-live). PreVote,
the maintainer's suggestion, would stop the term inflation but not restore delivery to node 4.
It is also outside the specs' scope (`PreVote' = false`, `Spec/go_etcd_io/raft/v3/NewRawNode.lean:116`,
`StartNode.lean:81`, `RestartNode.lean:62`).

Reproduction was not attempted. raftexample is gone at the pin, and the diagnosis rests on the
code above and the logs, not on the maintainer, who did not diagnose it. etcd's server does not
share the bug: on restart its transport peers come from the membership store
(`server/etcdserver/server.go:439`), and an applied snapshot re-adds them from the
snapshot's membership (`:1135`).

## Proposal

`transport-tracks-confstate` (low priority: the example is gone). State and prove, for etcd's
server, the invariant "after each `Ready` is processed, the transport's peer set is
raft's configuration (voters, learners, outgoing voters) minus self". Its parts are
`EtcdServer.applyConfChange` (now a trust-boundary axiom, `etc/tcb-baseline.txt`), the restart
path's peer setup from the membership store and the snapshot path's (`server.go:439`, `:1135`), and `rafthttp.Transport.{AddPeer,RemovePeer}`
specified as operations on an abstract peer set (a trust boundary). Cost: medium. The
membership store (`api/membership`) is not translated, and `rafthttp` is names-only.

## Files

None in `issues/` (the bug is in code removed before the pin, which nothing here translates).
