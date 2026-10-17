package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func review86Node(id uint64) *raft {
	cfg := newTestConfig(id, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	cfg.PreVote = true
	cfg.CheckQuorum = true
	return newRaft(cfg)
}

func pick(msgs []pb.Message, to uint64, ty pb.MessageType) []pb.Message {
	var out []pb.Message
	for _, m := range msgs {
		if m.To == to && m.Type == ty {
			out = append(out, m)
		}
	}
	return out
}

func stepAll(t *testing.T, r *raft, msgs []pb.Message) []pb.Message {
	for _, m := range msgs {
		if err := r.Step(m); err != nil {
			t.Fatal(err)
		}
	}
	return r.readMessages()
}

// Two nodes pre-campaign concurrently (PreVote + CheckQuorum, etcd's defaults); node 1 wins
// its election first and node 3 hears from it (lease) before node 2's MsgVote arrives.
// Before PR #86 both elections are at the same term r.Term+1 and node 2 simply becomes
// node 1's follower on its MsgApp. With PR #86 node 2's election term is an independent draw:
// when it is higher than node 1's, node 2 answers node 1's MsgApp with a higher-term
// MsgAppResp and deposes the freshly elected leader, while node 2 itself cannot win (its log
// lacks the new leader's empty entry, and node 3 is in node 1's lease).
// Returns (deposed, T1, T2).
func review86Race(t *testing.T) (bool, uint64, uint64) {
	n1, n2, n3 := review86Node(1), review86Node(2), review86Node(3)

	m1 := stepAll(t, n1, []pb.Message{{From: 1, To: 1, Type: pb.MsgHup}})
	m2 := stepAll(t, n2, []pb.Message{{From: 2, To: 2, Type: pb.MsgHup}})

	// node 1's pre-vote wins with node 3.
	r3 := stepAll(t, n3, pick(m1, 3, pb.MsgPreVote))
	mv1 := stepAll(t, n1, pick(r3, 1, pb.MsgPreVoteResp))
	if n1.state != StateCandidate {
		t.Fatalf("n1 not candidate: %v", n1.state)
	}
	// node 2's pre-vote wins with node 3 too (node 3 has no leader yet).
	r3 = stepAll(t, n3, pick(m2, 3, pb.MsgPreVote))
	mv2 := stepAll(t, n2, pick(r3, 2, pb.MsgPreVoteResp))
	if n2.state != StateCandidate {
		t.Fatalf("n2 not candidate: %v", n2.state)
	}
	T1, T2 := n1.Term, n2.Term

	// node 3 votes for node 1, node 1 becomes leader and appends its empty entry.
	r3 = stepAll(t, n3, pick(mv1, 3, pb.MsgVote))
	apps := stepAll(t, n1, pick(r3, 1, pb.MsgVoteResp))
	if n1.state != StateLeader {
		t.Fatalf("n1 not leader: %v", n1.state)
	}
	// node 3 receives the MsgApp: it follows node 1, in its lease.
	r3 = stepAll(t, n3, pick(apps, 3, pb.MsgApp))
	stepAll(t, n1, pick(r3, 1, pb.MsgAppResp))

	// node 2's MsgVote reaches nodes 1 and 3; node 1's MsgVote reaches node 2.
	stepAll(t, n3, pick(mv2, 3, pb.MsgVote))
	stepAll(t, n1, pick(mv2, 1, pb.MsgVote))
	stepAll(t, n2, pick(mv1, 2, pb.MsgVote))
	// node 1's MsgApp reaches node 2, and node 2's answer node 1.
	r2 := stepAll(t, n2, pick(apps, 2, pb.MsgApp))
	stepAll(t, n1, pick(r2, 1, pb.MsgAppResp))

	return n1.state != StateLeader, T1, T2
}

func TestReview86RaceDeposesNewLeader(t *testing.T) {
	deposed, kept := 0, 0
	for i := 0; i < 200; i++ {
		d, T1, T2 := review86Race(t)
		if d {
			deposed++
			if i < 3 || deposed == 1 {
				t.Logf("leader at %d deposed by losing candidate at %d", T1, T2)
			}
		} else {
			kept++
		}
	}
	t.Logf("of 200 races: leader deposed %d times, kept %d times", deposed, kept)
	if deposed > 0 {
		t.Errorf("a freshly elected leader was deposed by the concurrent (losing) candidate in %d/200 runs", deposed)
	}
}

// A pre-vote granted at T1 does not mean the election's (independent) term T2 is above the
// granter's term: node 2 (term P, a failed candidate of epoch 1, no entries at P) grants node 1's
// pre-vote at T1 > P, then ignores node 1's MsgVote at T2 <= P. Node 3 is down. Node 1 is left a
// candidate that cannot win this round (before PR #86, T1 = T2).
func TestReview86PreVoteGrantedVoteIgnored(t *testing.T) {
	stuck, runs := 0, 0
	for i := 0; i < 400; i++ {
		n1, n2 := review86Node(1), review86Node(2)
		P := uint64(0x1_8000)
		n2.becomeFollower(P, None)
		m1 := stepAll(t, n1, []pb.Message{{From: 1, To: 1, Type: pb.MsgHup}})
		pv := pick(m1, 2, pb.MsgPreVote)
		if pv[0].Term <= P {
			continue // pre-vote rejected: not this case
		}
		runs++
		r2 := stepAll(t, n2, pv)
		mv := stepAll(t, n1, pick(r2, 1, pb.MsgPreVoteResp))
		if n1.state != StateCandidate {
			t.Fatalf("pre-vote not won")
		}
		r2 = stepAll(t, n2, pick(mv, 2, pb.MsgVote))
		stepAll(t, n1, r2)
		if n1.state == StateCandidate && n2.Term == P {
			stuck++
			if stuck == 1 {
				t.Logf("pre-vote at %d granted by node at %d; vote at %d ignored", pv[0].Term, P, n1.Term)
			}
		}
	}
	t.Logf("%d of %d granted pre-votes led to an ignored election", stuck, runs)
	if stuck > 0 {
		t.Errorf("granted pre-vote, ignored vote: %d/%d", stuck, runs)
	}
}
