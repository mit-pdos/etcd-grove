package swift

import (
	"testing"

	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// F4: a fast-path get's result changes in the recovery. N = 5, ballot 0,
// leader 0, AQ(0) = {0, 1, 2}. The leader handles put d, put p, get x (x's
// result V_p). Replica 1 handles d (its descriptor has not run handlePropose
// when the report is made: START), then p and x (pre-accepted, x with
// dependencies [p], path [d, p, x]). Replica 2 handles p, gets the leader's
// ack of p (its synced path becomes [d, p]), handles x (dependencies [p],
// path [d, p, x]) and then d (pre-accepted, dependencies [p, x]). The client
// of x accepts V_p on the fast path. Replica 3 recovers with the reports of
// {1, 2, 3}: rule 2 keeps x (deps [p]); the closure takes p from replica 1
// (deps [d]) and d from replica 2 (PRE_ACCEPT beats replica 1's START: deps
// [p, x]): a cycle x -> p -> d -> x, broken at x, the smallest id.
func TestIssueF4_FastGetResultKept(t *testing.T) {
	rs := newNet(t, 5, 0)
	l, r1, r2, r3 := rs[0], rs[1], rs[2], rs[3]
	idx, idp, idd := cid(1, 0), cid(2, 0), cid(3, 0)
	pd, pp, px := put(idd, 7, "Vd"), put(idp, 7, "Vp"), get(idx, 7)

	for _, q := range []*defs.GPropose{pd, pp, px} {
		handle(l, q)
	}
	lacks, _ := batched(l)
	replyx := replyOf(t, l, idx)

	// replica 1: d's descriptor does not run its handlePropose (emulated: the
	// proposal reaches it while the status is not NORMAL)
	r1.status = RECOVERING
	handle(r1, pd)
	r1.status = NORMAL
	handle(r1, pp)
	handle(r1, px)
	_, f1 := batched(r1)

	handle(r2, pp)
	deliverAck(r2, ackOf(lacks, idp))
	handle(r2, px)
	_, f2 := batched(r2)
	handle(r2, pd)

	v, ok := accept(newTestClient(5), replyx, clientAckOf(f1, idx), clientAckOf(f2, idx))
	if !ok || v != "Vp" {
		t.Fatalf("schedule: the client did not accept x with Vp (%q, %v)", v, ok)
	}

	sync := recoverWith(r3, 3, r1, r2, r3)
	got, in := valueIn(sync, idx)
	if !in || got != "Vp" {
		t.Fatalf("MSync(3) order %v: x (accepted with Vp on the fast path) reads %q (kept: %v)",
			syncOrder(sync), got, in)
	}
}
