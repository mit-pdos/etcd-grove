package swift

import "testing"

// F2a (notes/interface-findings.md): handleSync did not reset the hash logs.
// A command a replica appended in an earlier ballot and no leader
// acknowledged stayed in its pending list, and its later path hashes chained
// over it: a follower that received that command fresh in the new ballot could
// produce the leader's path hash while its own sequence had the command
// before the leader's, and a get accepted on the fast path was re-executed
// after another put.
//
// N = 3; put q (client 1), put p (client 2), get x (client 3) of one key.
// Ballot 0: replica 2 (outside AQ(0) = {0, 1}) handles q. Replica 2 recovers
// (ballot 5, AQ(5) = {1, 2}) with the reports of {1, 2}: MSync(5) lacks q (its
// re-proposal is delayed). The leader 2 handles p, then x (its hash log still
// has q pending); replica 0 accepts p; replica 1 receives q, p, x before any
// of the leader's acks: x's dependencies [p] and path [q, p, x] are the
// leader's, and client 3 accepts x with the leader's result V2. Replica 1
// recovers (ballot 7) with the reports of {0, 1}. Whatever result client 3
// accepted, the MSync must give x that result.
func TestIssueF2a_StaleHashLog(t *testing.T) {
	rs := newNet(t, 3, 0)
	idq, idp, idx := cid(1, 0), cid(2, 0), cid(3, 0)
	q, p, x := put(idq, 7, "V1"), put(idp, 7, "V2"), get(idx, 7)

	handle(rs[2], q)
	sync5 := recoverWith(rs[2], 5, rs[1], rs[2])
	if _, in := sync5.Phases[idq]; in {
		t.Fatalf("schedule: MSync(5) has q: %v", sync5.Phases)
	}
	for _, r := range rs {
		r.handleSync(sync5)
	}

	l, f, o := rs[2], rs[1], rs[0]
	handle(l, p)
	handle(l, x)
	lacks, _ := batched(l)
	replyX := replyOf(t, l, idx)

	handle(o, p)
	deliverAck(o, ackOf(lacks, idp))

	handle(f, q)
	handle(f, p)
	handle(f, x)
	_, facks := batched(f)
	v, accepted := accept(newTestClient(3), replyX, clientAckOf(facks, idx))

	sync7 := recoverWith(f, 7, o, f)
	w, in := valueIn(sync7, idx)
	if accepted && (!in || w != v) {
		t.Fatalf("client 3 accepted x with %q in ballot 5; MSync(7) (order %v) gives it %q (kept %v)",
			v, syncOrder(sync7), w, in)
	}
}
