package register

import (
	"context"
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
// unstamped; a replication, election or read-index message: pre-vote and snapshots are
// off), from a node to another, of a term (but the forwarded ones, which carry none), and
// with no context but on a heartbeat or its response, where it is the leader's read-index
// position (the cluster never transfers leadership, the context's other use). raft sends
// nothing else, but what it promises of a Ready's messages does not say so.
func deliverable(m pb.Message) bool {
	switch m.Type {
	case pb.MsgProp:
	case pb.MsgReadIndex:
		if m.Term != 0 {
			return false
		}
	case pb.MsgApp, pb.MsgAppResp, pb.MsgVote, pb.MsgVoteResp, pb.MsgReadIndexResp:
		if m.Term == 0 {
			return false
		}
	case pb.MsgHeartbeat, pb.MsgHeartbeatResp:
		if m.Term == 0 {
			return false
		}
		return m.From != 0 && m.From != m.To
	default:
		return false
	}
	return m.From != 0 && m.From != m.To && m.Context == nil
}

// deliver passes the deliverable messages to their targets among peers, each its own copy
// (the receiver may adopt the entries slice); a message to an unknown node is dropped, as
// is the error of Step.
func deliver(peers map[uint64]raft.Node, ms []pb.Message) {
	for _, m := range ms {
		if !deliverable(m) {
			continue
		}
		nd, ok := peers[m.To]
		if !ok {
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
// specification states its value with lower bounds on the register's history.
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
	send := func(ms []pb.Message) {
		deliver(peers, ms)
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
}
