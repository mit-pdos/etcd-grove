package swift

import (
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

// N4 (stage 1 review, R2's note): a fast quorum is a set of |FQ| distinct
// replicas, and the fast path needs each non-leader member's matching hash.
// Under fast reads the leader sends a read's MFastAckClient (handlePropose's
// isRead branch) and, once it executed it, the MReply. The client counted the
// leader twice: its MReply as the leader message and its own fast ack as a
// member's (MsgSet keys the members by replica id, the leader message apart).
//
// Ballot 0, leader 0: the leader's ack and reply, in either order, then the
// other members' acks one at a time; the client accepts only once |FQ|
// distinct replicas (the leader among them) have matching hashes.
func TestIssueN4_LeaderCountedOnce(t *testing.T) {
	h := []SHash{{H: [32]byte{1}}}
	for _, n := range []int{3, 5} {
		for _, replyFirst := range []bool{false, true} {
			c := newTestClient(n)
			x := cid(1, 0)
			ack := func(rep int32) {
				f := newFastAck()
				f.Replica, f.Ballot, f.CmdId, f.Checksum = rep, 0, x, h
				c.handleFastAck(f, false)
			}
			reply := func() {
				c.handleReply(&MReply{Replica: 0, Ballot: 0, CmdId: x, Checksum: h,
					Rep: state.Value("v")})
			}
			accepted := func() bool {
				select {
				case <-c.Reply:
					return true
				default:
					return false
				}
			}
			if replyFirst {
				reply()
				ack(0)
			} else {
				ack(0)
				reply()
			}
			fq := n/2 + 1
			for rep := int32(1); rep < int32(fq); rep++ {
				if accepted() {
					t.Fatalf("N=%d, reply first %v: accepted with %d distinct replicas (fast quorum %d)",
						n, replyFirst, rep, fq)
				}
				ack(rep)
			}
			if !accepted() {
				t.Fatalf("N=%d, reply first %v: not accepted with %d distinct replicas",
					n, replyFirst, fq)
			}
		}
	}
}
