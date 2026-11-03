---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/raft#52 pr merged: introduced the probe-to-replicate shortcut (`pr.Match == m.Index && pr.State == StateProbe`) and the `TestLeaderAppResp` case that pins the index-0 ack; does not consider the stale-term response
  - etcd-io/raft#148 issue closed: related, not this bug: a delayed (rejected) `MsgAppResp` misread in `StateProbe`
  - etcd-io/raft#149 pr merged: the fix of #148; does not touch the shortcut
blocks-proof: yes
---

# raft: after a delayed stale-term message, a new leader sends a snapshot to a follower that is already caught up

After a leader change, a new leader can send a full snapshot (or, with an uncompacted log, the
whole log from index 1) to a follower whose log already matches its own. With check-quorum or
pre-vote on (as etcd runs), a follower answers a delayed `MsgApp` or heartbeat of an older term
with an empty response of its own term; when the sender has meanwhile become leader in that term
and has not yet heard from the follower, it reads that response as an acknowledgement of index 0.

**Expected:** the leader should keep probing the follower and send it only the entries it lacks:
the empty response exists [to carry the higher term](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1133-L1156)
and acknowledges nothing.

**Impact:** one unnecessary snapshot transfer to one follower after a leader change, when the old
leader's append or heartbeat to it is delayed past the election (rafthttp sends appends and votes
on different streams, so they are not ordered) and the follower's empty answer reaches the new
leader before its answer to the leader's probe. In etcd the log is compacted from the first
in-memory snapshot on ([`compactRaftLog`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L2146-L2149)
compacts at index 1 even below `SnapshotCatchUpEntries`), so the leader sends its whole database
as a snapshot. Performance only: no wrong result. Same code in v3.7.0.

**Reproduction:** `TestLeaderIndexZeroAckSendsNoSnapshot` in
[`issues/raft-stale-term-appresp-index-zero-ack/index_zero_ack_test.go`](raft-stale-term-appresp-index-zero-ack/index_zero_ack_test.go)
(a leader of term 2 over a log compacted at index 1, peer 2 still probing, steps the response that
`TestStaleMsgAppGetsIndexZeroAck`, in the same file and passing, shows a follower sends), copied
into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64:

```
$ go test . -run '^(TestStaleMsgAppGetsIndexZeroAck|TestLeaderIndexZeroAckSendsNoSnapshot)$' -count=1 -v
    index_zero_ack_test.go:69:
        	Error:      	Should not be: 7
        	Test:       	TestLeaderIndexZeroAckSendsNoSnapshot
        	Messages:   	1->2 MsgSnap Term:2 Log:0/0
        	            	  Snapshot: Index:3 Term:1 ConfState:Voters:[1 2 3] VotersOutgoing:[] Learners:[] LearnersNext:[] AutoLeave:false
--- FAIL: TestLeaderIndexZeroAckSendsNoSnapshot (0.00s)
FAIL
```

**Cause:** for a non-rejected `MsgAppResp`, `stepLeader` moves a probing peer to replicate when
[`pr.Match == m.Index`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1519),
a shortcut meant for a caught-up follower probed after `ReportUnreachable`. A peer the new leader
has not heard from has `Match` 0, so the index-0 answer matches; `BecomeReplicate` sets `Next` to
1, and `term(0)` being compacted, the leader [sends a snapshot](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L666-L690).

## Proof

yes: the verified raft carries the fix (the fork's `c8217eb9` on `raft37-goose-lean-a1`,
`etc/goose.py`); without it the tracker invariant `pr.Next >= 2` that excludes `MsgSnap` in a
static etcd cluster is false (`notes/decisions.md`, "D21 M0: the no-`MsgSnap` argument checked").

## Fix

No fix branch off upstream `main`: [`fix.patch`](raft-stale-term-appresp-index-zero-ack/fix.patch)
(the fork commit, on v3.7.0) takes the shortcut only when the probe is at the acked index
(`&& pr.Next == pr.Match+1`). It changes upstream's own `TestLeaderAppResp` fourth case, which
expects the index-0 ack to move a peer probing at `Next = 3` back to `Next = 1`; a PR has to argue
that expectation is wrong. The alternative, answering a stale-term message with `Reject: true`,
changes the wire behavior older peers see.
