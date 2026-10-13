package register

import (
	"context"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// quietLogger is a raft.Logger that discards what raft logs; Fatal and Panic panic, as raft
// expects of them.
type quietLogger struct{}

func (quietLogger) Debug(v ...interface{})                   {}
func (quietLogger) Debugf(format string, v ...interface{})   {}
func (quietLogger) Error(v ...interface{})                   {}
func (quietLogger) Errorf(format string, v ...interface{})   {}
func (quietLogger) Info(v ...interface{})                    {}
func (quietLogger) Infof(format string, v ...interface{})    {}
func (quietLogger) Warning(v ...interface{})                 {}
func (quietLogger) Warningf(format string, v ...interface{}) {}
func (quietLogger) Fatal(v ...interface{})                   { panic("raft: fatal") }
func (quietLogger) Fatalf(format string, v ...interface{})   { panic(format) }
func (quietLogger) Panic(v ...interface{})                   { panic("raft: panic") }
func (quietLogger) Panicf(format string, v ...interface{})   { panic(format) }

// deliverable says whether the transport passes m on: a message of a type a node of the
// cluster sends its peers (a proposal or a read-index request forwarded to the leader,
// unstamped; a replication, election or read-index message, or a leader's MsgTimeoutNow to
// the target of a leadership transfer, which carries nothing: pre-vote and snapshots are
// off), from a node to another, of a term (but the forwarded ones, which carry none), and
// with no context but on a heartbeat or its response, where it is the leader's read-index
// position, or on a vote request, where it marks a transfer's campaign. raft sends nothing
// else but a transfer request a follower forwards to its leader (MsgTransferLeader, stamped
// with the follower's term), which the transport drops: a transfer is asked of the leader
// itself (Register.TransferLeadership). What raft promises of a Ready's messages does not
// say that it sends nothing else.
func deliverable(m pb.Message) bool {
	switch m.Type {
	case pb.MsgProp:
	case pb.MsgReadIndex:
		if m.Term != 0 {
			return false
		}
	case pb.MsgApp, pb.MsgAppResp, pb.MsgVoteResp, pb.MsgReadIndexResp:
		if m.Term == 0 {
			return false
		}
	case pb.MsgTimeoutNow:
		if m.Term == 0 || m.Entries != nil {
			return false
		}
	case pb.MsgVote, pb.MsgHeartbeat, pb.MsgHeartbeatResp:
		if m.Term == 0 {
			return false
		}
		return m.From != 0 && m.From != m.To
	default:
		return false
	}
	return m.From != 0 && m.From != m.To && m.Context == nil
}

// timeouts bounds the MsgTimeoutNow the transport passes on: each makes its target campaign
// at once, raising its term as an election timeout would, and the terms must stay below
// 2^64 (as ticks bounds a node's ticks).
const timeouts = 1 << 20

// transfers counts the MsgTimeoutNow the transport may still pass on.
type transfers struct {
	mu   sync.Mutex
	left uint64
}

// take uses one of them up; false when none is left.
func (t *transfers) take() bool {
	t.mu.Lock()
	ok := t.left != 0
	if ok {
		t.left--
	}
	t.mu.Unlock()
	return ok
}

// deliver passes the deliverable messages to their targets among peers, each its own copy
// (the receiver may adopt the entries slice), and a MsgTimeoutNow only while tr has one
// left; a message to an unknown node is dropped, as is the error of Step.
func deliver(peers map[uint64]raft.Node, tr *transfers, ms []pb.Message) {
	for _, m := range ms {
		if !deliverable(m) {
			continue
		}
		nd, ok := peers[m.To]
		if !ok {
			continue
		}
		if m.Type == pb.MsgTimeoutNow && !tr.take() {
			continue
		}
		m.Entries = append([]pb.Entry(nil), m.Entries...)
		nd.Step(context.Background(), m)
	}
}

const (
	tickInterval = 5 * time.Millisecond
	// ticks bounds the ticks of a node (an hour and a half of them): each moves raft's
	// clock, and the terms it starts must stay below 2^64.
	ticks = 1 << 20
)

// tick drives a node's clock.
func tick(nd raft.Node) {
	for i := 0; i < ticks; i++ {
		time.Sleep(tickInterval)
		nd.Tick()
	}
}

// Main runs a cluster of three replicas connected in process: client A puts "hello" on
// replica 1 and then tells client B, which gets the value on replica 2; since A's Put
// completed before B's Get began and nobody else puts, B sees "hello". B then reads by
// read index on replica 3 (Read), which goes through the transport's read-index messages
// and heartbeat contexts; its value is "hello" as well, but Main does not check it: Read's
// specification states its value with lower bounds on the register's history. Last, B asks
// every replica to hand the leadership over to replica 3: the leader does, through the
// transport's MsgTimeoutNow and the vote requests of a transfer's campaign (the followers'
// requests are dropped). Nothing follows it: an operation during the transfer could wait
// forever (a proposal forwarded to a leader that is transferring is dropped, and do does not
// retry it; a read index asked of a node that knows no leader is dropped, and Read does not
// retry it).
func Main() {
	voters := []uint64{1, 2, 3}
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := NewStorage(voters)
		peers[id] = raft.RestartNode(&raft.Config{
			ID:              id,
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	send := func(ms []pb.Message) {
		deliver(peers, tr, ms)
	}
	regs := make(map[uint64]*Register)
	for _, id := range voters {
		regs[id] = New(id, peers[id], storages[id], send)
		go tick(peers[id])
	}

	done := make(chan bool, 1)
	go func() {
		regs[1].Put("hello")
		done <- true
	}()
	<-done
	if regs[2].Get() != "hello" {
		panic("register: a Get after a Put did not see its value")
	}
	regs[3].Read()
	regs[1].TransferLeadership(3)
	regs[2].TransferLeadership(3)
	regs[3].TransferLeadership(3)
}
