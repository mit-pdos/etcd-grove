package swift

import (
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

// C3: the client's fast (and slow) quorum must be acks of the ballot of the
// leader's reply it completes: a fast ack of ballot b is a pre-accept of
// ballot b's fast quorum, not of another ballot's. The client compared only
// the hashes, and ignored an older ballot's ack only once it had seen a
// higher ballot.
//
// Three replicas: replica 1's fast ack of ballot 0 arrives first, then
// ballot 3's leader's reply with the same hashes: no quorum of ballot 3.
func TestIssueC3_AcksOfTheLeadersBallot(t *testing.T) {
	c := newTestClient(3)
	x := cid(1, 0)
	h := []SHash{{H: [32]byte{1}}}
	f := newFastAck()
	f.Replica, f.Ballot, f.CmdId, f.Checksum = 1, 0, x, h
	c.handleFastAck(f, false)
	c.handleReply(&MReply{Replica: 0, Ballot: 3, CmdId: x, Checksum: h, Rep: state.Value("v")})
	select {
	case r := <-c.Reply:
		t.Fatalf("accepted %q with an ack of ballot 0 and the reply of ballot 3", r.Val)
	default:
	}

}
