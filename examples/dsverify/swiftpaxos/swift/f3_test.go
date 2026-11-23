package swift

import (
	"io"
	"log"
	"os"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/state"
)

// newNet is n in-memory replicas at ballot b (sequential descriptors, reply
// channels running; the test carries the messages between them).
func newNet(t *testing.T, n int, b int32) []*Replica {
	seqDescs(t)
	log.SetOutput(io.Discard)
	t.Cleanup(func() { log.SetOutput(os.Stderr) })
	rs := []*Replica{}
	for i := 0; i < n; i++ {
		rs = append(rs, newTestReplica(t, n, int32(i), b, true))
	}
	return rs
}

// handle is run's propose case for one proposal (directly: handleSync's
// re-proposals also feed ProposeChan, and the test delays those).
func handle(r *Replica, p *defs.GPropose) {
	r.handleProposal(p)
}

// batched takes the fast acks r gave its batcher: the leader's MFastAcks, and
// a fast-quorum follower's MFastAckClients as the batcher builds them.
func batched(r *Replica) ([]*MFastAck, []*MFastAckClient) {
	acks := []*MFastAck{}
	toClient := []*MFastAckClient{}
	for {
		select {
		case op := <-r.batcher.fastAcks:
			f := op.msg.(*MFastAck)
			if op.sendToClient {
				toClient = append(toClient, &MFastAckClient{Replica: f.Replica, Ballot: f.Ballot,
					CmdId: f.CmdId, Checksum: clientChecksum(f.Checksum, f.Dep)})
			} else {
				acks = append(acks, copyFastAck(f))
			}
		default:
			return acks, toClient
		}
	}
}

func ackOf(acks []*MFastAck, x CommandId) *MFastAck {
	for _, a := range acks {
		if a.CmdId == x {
			return a
		}
	}
	return nil
}

func clientAckOf(acks []*MFastAckClient, x CommandId) *MFastAckClient {
	for _, a := range acks {
		if a.CmdId == x {
			return a
		}
	}
	return nil
}

// deliverAck is run's fast-ack case at r for the leader's ack f.
func deliverAck(r *Replica, f *MFastAck) {
	r.leaderAckHash(f)
	r.getCmdDescSeq(f.CmdId, copyFastAck(f), nil, nil, r.leader() == r.Id)
}

// replyOf waits for the MReply of x that the leader r's reply channel sends
// (the other messages r sent are dropped).
func replyOf(t *testing.T, r *Replica, x CommandId) *MReply {
	for i := 0; i < 5000; i++ {
		for _, m := range sent(r) {
			if rep, ok := m.(*MReply); ok && rep.CmdId == x {
				return rep
			}
		}
		time.Sleep(time.Millisecond)
	}
	t.Fatalf("no MReply of %v", x)
	return nil
}

// accept gives a client the leader's reply and the followers' fast acks of
// one command (as its handleMsgs does) and says whether it accepted, with
// which result.
func accept(c *Client, reply *MReply, acks ...*MFastAckClient) (string, bool) {
	c.handleReply(reply)
	for _, a := range acks {
		f := newFastAck()
		f.Replica, f.Ballot, f.CmdId, f.Checksum = a.Replica, a.Ballot, a.CmdId, a.Checksum
		c.handleFastAck(f, false)
	}
	select {
	case r := <-c.Reply:
		return string(r.Val), true
	default:
		return "", false
	}
}

// recoverWith is nl's recovery to ballot b with the reports of reps (each
// fillNewLeaderAckN at its cballot): the MSync it computes.
func recoverWith(nl *Replica, b int32, reps ...*Replica) *MSync {
	msgs := []interface{}{}
	for _, r := range reps {
		m := &MNewLeaderAckN{Replica: r.Id, Ballot: b, Cballot: r.cballot}
		r.fillNewLeaderAckN(m)
		msgs = append(msgs, m)
	}
	nl.repchan.stop()
	nl.status = RECOVERING
	nl.ballotL.Lock()
	nl.ballot = b
	nl.ballotL.Unlock()
	return nl.recoveredSync(msgs)
}

func indexOf(ids []CommandId, x CommandId) int {
	for i, id := range ids {
		if id == x {
			return i
		}
	}
	return -1
}

// valueIn is x's result (a get's: the value of the last put of its key
// before it) in the order every replica executes msg in.
func valueIn(msg *MSync, x CommandId) (string, bool) {
	val := ""
	for _, id := range syncOrder(msg) {
		cmd := msg.Cmds[id]
		if cmd.K != msg.Cmds[x].K {
			continue
		}
		if id == x {
			return val, true
		}
		if cmd.Op == state.PUT {
			val = string(cmd.V)
		}
	}
	return "", false
}

// F3 (notes/interface-findings.md; etc/modelcheck/f3.py): a recovery ordered
// a put invoked after a completed fast-path put before it. Rule 2 kept the
// fast quorum reporter's two pre-accepted puts with its own dependencies and
// ordered them by ids: the reporter's order between them was lost (rule 1
// had replaced the dependencies of the put between them by the leader's).
//
// N = 3, ballot 0, leader 0, AQ(0) = {0, 1}; four puts of one key, ids by
// client 1 < 2 < 3 < 4. The leader handles put1, put2, put4; replica 2
// accepts put1 and put2; at replica 1 the leader's acks of put1 and put2
// arrive before their proposals, then it handles put2 and put4: put4's path
// and dependencies are the leader's, and client 4 accepts put4 (fast path).
// Then client 3 invokes put3, which reaches replica 1 only, after put1's
// delayed proposal. Replica 1 recovers (ballot 4) with the reports of {1, 2}.
// put4 completed before put3 was invoked: every linearization has put4 before
// put3, so the MSync must too (otherwise a get after put3 returned reads V4).
func TestIssueF3_RealTimeOrderKept(t *testing.T) {
	rs := newNet(t, 3, 0)
	l, f, o := rs[0], rs[1], rs[2]
	id1, id2, id3, id4 := cid(1, 0), cid(2, 0), cid(3, 0), cid(4, 0)
	p1, p2, p3, p4 := put(id1, 7, "V1"), put(id2, 7, "V2"), put(id3, 7, "V3"), put(id4, 7, "V4")

	for _, p := range []*defs.GPropose{p1, p2, p4} {
		handle(l, p)
	}
	lacks, _ := batched(l)
	reply4 := replyOf(t, l, id4)

	handle(o, p1)
	handle(o, p2)
	deliverAck(o, ackOf(lacks, id1))
	deliverAck(o, ackOf(lacks, id2))

	deliverAck(f, ackOf(lacks, id1))
	deliverAck(f, ackOf(lacks, id2))
	handle(f, p2)
	handle(f, p4)
	_, facks := batched(f)
	if _, ok := accept(newTestClient(3), reply4, clientAckOf(facks, id4)); !ok {
		t.Fatal("schedule: client 4 did not accept put4 on the fast path")
	}

	// put3 is invoked after put4 returned
	handle(f, p1)
	handle(f, p3)

	sync := recoverWith(f, 4, f, o)
	order := syncOrder(sync)
	i3, i4 := indexOf(order, id3), indexOf(order, id4)
	if i4 < 0 || i3 >= 0 && i3 < i4 {
		t.Fatalf("MSync(4) order %v: put3, invoked after put4 returned, is before it "+
			"(a get after put3 returned reads V4)", order)
	}
}
