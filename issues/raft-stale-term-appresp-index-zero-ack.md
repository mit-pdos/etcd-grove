---
upstream: unchecked
links:
---

# raft: a leader reads the empty `MsgAppResp` answering a stale-term append as an ack of index 0

- **Status**: a liveness/performance bug, not a safety bug. A voter answers a `MsgApp` or
  `MsgHeartbeat` of a lower term (check-quorum or pre-vote on, as etcd configures raft) with an
  empty `MsgAppResp` of its own term, whose `Index` is 0 and `Reject` false. Its purpose is only to
  carry the higher term. If the stale sender has meanwhile become leader *at that same term* and
  has not yet heard from the voter (its progress is `StateProbe`, `Match = 0`), it takes the
  response as an acknowledgement of index 0 and moves the peer to `StateReplicate` with `Next = 1`.
  It then replicates the whole log from index 1 to a follower that may be fully caught up. If its
  log is compacted at all, `term(0)` is gone and it sends a `MsgSnap` instead, as etcd's servers do
  after their first in-memory snapshot (`compactRaftLog` compacts at index 1 even when
  `appliedi <= SnapshotCatchUpEntries`). Reproduced by two Go tests (below). Upstream not
  searched.
- **Where** (etcd-io/raft v3.7.0 `b867cf13` as in the fork's `raft37-goose-lean` `509271dac`,
  the revision `etc/goose.py` pins; line numbers of that tree):
  - `raft.go:1133-1156` (`Step`, `m.Term < r.Term`): with `checkQuorum || preVote`, a stale
    `MsgHeartbeat`/`MsgApp` gets `r.send(&pb.Message{To: m.From, Type: pb.MsgAppResp.Enum()})`, sent
    at `r.Term` with `Index` 0 and no `Reject`.
  - `raft.go:1519-1522` (`stepLeader`, `MsgAppResp`, not rejected): `pr.MaybeUpdate(m.Index) ||
    (pr.Match == m.Index && pr.State == StateProbe)` and then `pr.BecomeReplicate()`. With
    `Match = 0 = m.Index`, the second disjunct holds.
  - `tracker/progress.go:146-149` (`BecomeReplicate`: `Next = Match + 1`, here 1), then
    `raft.go:1561` (`for r.maybeSendAppend(...)`), `raft.go:624-629` (`term(Next - 1)` fails
    with `ErrCompacted` when the first index is past 1) and `raft.go:666-690`
    (`maybeSendSnapshot`: `RecentActive` was just set by the response, `raft.go:1380`).
  - etcd (`8a24be2a3`): `server/etcdserver/server.go:2155-2160` (`compacti := uint64(1)` unless
    `snapi > SnapshotCatchUpEntries`), called after every snapshot (`server.go:1220-1228`), and
    an in-memory snapshot is taken every 100 applied entries (`server.go:116, 1235-1236`).
- **What happens**: node 1 is leader at term 1 and sends node 2 a `MsgApp` (or heartbeat), which
  is delayed. rafthttp sends appends on the `msgappv2` stream and votes on the `message` stream,
  so the two are not ordered. Node 1 loses leadership, campaigns at term 2 and wins with node 2's
  vote, so node 2 is at term 2. The term-1 message then reaches node 2, which answers with
  `MsgAppResp{Term: 2, Index: 0}`. That answer reaches node 1 before node 2's answer to node 1's
  term-2 probe. Node 1 moves node 2 to `StateReplicate` with `Next = 1`. With an uncompacted log it
  resends the log from index 1. With a log compacted at any index (etcd: after 101 applied
  entries) it sends node 2 its latest snapshot (`StateSnapshot`), although node 2's log may
  already match the leader's.
  Reproduction (in package `raft`, next to `raft_test.go`; the second test fails at the pinned
  revision, the first documents the response):

  ```go
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A follower at term 2 answers a stale MsgApp of term 1 (check-quorum on) with
// an empty MsgAppResp of its own term: Index 0, not a rejection.
func TestStaleMsgAppGetsIndexZeroAck(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s.Append(index(1).terms(1, 1, 1)); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(2, 10, 1, s)
	r.checkQuorum = true
	r.becomeFollower(2, None) // voted in term 2, no leader heard yet
	r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
		Type: pb.MsgApp.Enum(), Index: new(uint64(3)), LogTerm: new(uint64(1))})
	msgs := r.readMessages()
	if len(msgs) != 1 || msgs[0].GetType() != pb.MsgAppResp || msgs[0].GetTo() != 1 ||
		msgs[0].GetTerm() != 2 || msgs[0].GetIndex() != 0 || msgs[0].GetReject() {
		t.Fatalf("unexpected response %v", msgs)
	}
}

// A leader of term 2 that has not yet heard from peer 2 (StateProbe, Match 0)
// reads that response as an ack of index 0: it moves 2 to StateReplicate with
// Next = 1. With its log compacted at index 1 (etcd's compactRaftLog after its
// first in-memory snapshot), term(0) is compacted and the leader sends 2 a
// MsgSnap although 2 holds the whole log.
func TestLeaderIndexZeroAckSendsSnapshot(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s.Append(index(1).terms(1, 1, 1)); err != nil {
		t.Fatal(err)
	}
	s.SetHardState(&pb.HardState{Term: new(uint64(1)), Commit: new(uint64(3))})
	cs := &pb.ConfState{Voters: []uint64{1, 2, 3}}
	if _, err := s.CreateSnapshot(3, cs, nil); err != nil {
		t.Fatal(err)
	}
	if err := s.Compact(1); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	r.checkQuorum = true
	r.becomeCandidate() // term 2
	r.becomeLeader()
	r.readMessages()
	if pr := r.trk.Progress[2]; pr.State.String() != "StateProbe" || pr.Match != 0 || pr.Next != 4 {
		t.Fatalf("after becomeLeader: %v", pr)
	}
	r.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)), Type: pb.MsgAppResp.Enum()})
	pr := r.trk.Progress[2]
	t.Logf("progress of 2 after the index-0 ack: %v", pr)
	for _, m := range r.readMessages() {
		if m.GetType() == pb.MsgSnap && m.GetTo() == 2 {
			t.Errorf("leader sends MsgSnap (index %d) to an up-to-date follower; progress %v",
				m.GetSnapshot().GetMetadata().GetIndex(), pr)
		}
	}
}
  ```

  `PATH=/usr/local/go/bin:$PATH GOTOOLCHAIN=go1.27.1 go test -run 'TestStaleMsgAppGetsIndexZeroAck|TestLeaderIndexZeroAckSendsSnapshot' .`:
  the first passes. The second fails with `progress of 2 after the index-0 ack: StateSnapshot
  match=0 next=4 paused pendingSnap=3` and `leader sends MsgSnap (index 3) to an up-to-date
  follower`.
- **Expected**: the higher-term response exists to make a stale leader step down (the comment at
  `raft.go:1137-1155`). Its `Index` acknowledges nothing, so a leader of the same term should not
  take it as an ack. `stepLeader`'s probe-to-replicate shortcut (for a follower that is caught up
  but probing after `ReportUnreachable`, `heartbeat_rep_recovers_from_probing.txt`) assumes that
  the acked index is the one being probed.
- **How the proof handles it**: not yet reached. Today the server is one member (`bootOk`'s
  `"%Hone"`, `InvBoot.lean:147-149`), so raft has no peer to probe. D21c (A) planned to exclude
  `MsgSnap` in an N-member cluster through a tracker invariant `pr.Next >= 2`. This bug falsifies
  that invariant (`notes/decisions.md`, "D21 M0: the no-`MsgSnap` argument checked").
- **Possible fixes**: (1) in `stepLeader`, take the shortcut only when the probe is at the acked
  index: `pr.Match == m.Index && pr.State == StateProbe && pr.Next == pr.Match+1`. This keeps
  `heartbeat_rep_recovers_from_probing`, where `Next = Match + 1` after `BecomeProbe`. (2) Mark
  the stale-term answer so that it cannot act as an ack: `Reject: true` with `Index` 0 makes
  `MaybeDecrTo` treat it as stale whenever `Next > 1`. This changes a wire behavior that older
  peers may rely on, so (1) is the smaller fix. Upstream's own test pins the current behavior:
  `TestLeaderAppResp`'s fourth case (`raft_test.go:2243-2248`, "Follower is StateProbing at 0, it
  sends MsgAppResp for 0 ... moved to StateReplicate", with `Next = 3` before the response, so the
  probe was not at 0) expects `Next = 4` and one `MsgApp` from index 0. With fix (1), raft's whole
  suite passes except that case, which gets `Next = 3` and no message (checked on a copy of the
  pinned tree). A fix therefore has to argue that this case's expectation is wrong.
- **Fixed in the fork**: fix (1), commit `c8217eb91ae5948182c1035ff0464b1e54b8f1d0` on branch
  `raft37-goose-lean-a1` of `upamanyus/etcd` (on `509271dac`; D21c′ (A1)), with
  `TestLeaderAppResp`'s fourth case updated (`Next = 3`, no message) and the two tests above as
  regression tests (the second as `TestLeaderIndexZeroAckSendsNoSnapshot`, asserting the peer
  stays `StateProbe`, `Match = 0`, `Next = 4`, with no `MsgSnap`). raft's whole suite (`go test
  ./...`, go1.27.1) passes; without the `raft.go` change, `TestLeaderAppResp` and
  `TestLeaderIndexZeroAckSendsNoSnapshot` fail. Goose translates it (only `stepLeader`'s
  condition changes, plus line numbers in later doc comments). Patch:
  `raft-stale-term-appresp-index-zero-ack.fix.patch`. Not yet pinned in `etc/goose.py` (D21 M3,
  phase 2).
- **Found**: 2026-10-19, in D21's stage M0, while checking by hand that a leader of a static
  etcd cluster never sends `MsgSnap`. Reproduced with the tests above.
