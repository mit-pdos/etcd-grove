package swift

import (
	"testing"

	"github.com/imdea-software/swiftpaxos/client"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/state"
)

// newTestClient is NewClient over a client without connections: its
// handleMsgs goroutine waits on channels nobody feeds, and a test calls the
// handlers.
func newTestClient(n int) *Client {
	b := &client.BufferClient{
		Client: &client.Client{Logger: &dlog.Logger{}},
		Reply:  make(chan *client.ReqReply, 16),
	}
	return NewClient(b, n)
}

// C4: the value a client returns must be the result in the leader's reply
// whose acks completed the quorum. The client kept one value for all
// replies, set by every MReply: a late MReply of an older ballot, whose acks
// the client no longer counts, changed it.
//
// Three replicas. Ballot 3's leader replies "v2"; ballot 0's (late) reply
// "v1" arrives; a slow ack of ballot 3 completes ballot 3's quorum.
func TestIssueC4_ValueOfTheCompletingReply(t *testing.T) {
	c := newTestClient(3)
	x := cid(1, 0)
	c.handleReply(&MReply{Replica: 0, Ballot: 3, CmdId: x, Rep: state.Value("v2")})
	c.handleReply(&MReply{Replica: 0, Ballot: 0, CmdId: x, Rep: state.Value("v1")})
	c.handleLightSlowAck(&MLightSlowAck{Replica: 1, Ballot: 3, CmdId: x})
	select {
	case r := <-c.Reply:
		if string(r.Val) != "v2" {
			t.Fatalf("returned %q, want ballot 3's result v2", r.Val)
		}
	default:
		t.Fatal("no reply")
	}
}
