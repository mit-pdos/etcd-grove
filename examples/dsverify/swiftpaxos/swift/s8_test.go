package swift

import "testing"

// S8: with the fast-ack pool (pool level 2), an ack must go back to the pool
// only when nothing refers to it. The leader's fast ack (and a slow ack) is
// added to both of a descriptor's message sets; freeing the sets (the
// descriptor's end) released it twice: two later acks were one object.
func TestIssueS8_AckReleasedOnce(t *testing.T) {
	if raceOn {
		// sync.Pool drops objects at random under the race detector, and
		// useFastAckPool is a package variable other tests' goroutines read
		t.Skip("not under -race")
	}
	seqDescs(t)
	useFastAckPool = true
	defer func() { useFastAckPool = false }()
	r := newTestReplica(t, 3, 1, 0, false)
	c := cid(1, 0)
	propose(r, put(c, 2, "x"))
	desc := r.getCmdDesc(c, nil, nil)
	ack := newFastAck()
	ack.Replica, ack.Ballot, ack.CmdId, ack.Dep = 0, 0, c, []CommandId{}
	ack.Checksum = []SHash{{}}
	r.handleFastAck(ack, desc)
	desc.slowPathH.Free()
	desc.fastPathH.Free()
	seen := map[*MFastAck]bool{}
	for i := 0; i < 4; i++ {
		a := newFastAck()
		if seen[a] {
			t.Fatalf("newFastAck returned the same ack twice")
		}
		seen[a] = true
	}
}
