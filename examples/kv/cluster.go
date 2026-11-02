package kv

import (
	"context"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
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
// the target of a leadership transfer, which carries nothing: pre-vote is off), from a node to another, of a term (but the forwarded ones, which carry none), and
// with no context but on a heartbeat or its response, where it is the leader's read-index
// position, or on a vote request, where it marks a transfer's campaign; and a leader's snapshot
// (MsgSnap: of a term, carrying a snapshot, of an index below maxIndex, no context). raft sends nothing
// else but a transfer request a follower forwards to its leader (MsgTransferLeader, stamped
// with the follower's term), which the transport drops: a transfer is asked of the leader
// itself (Register.TransferLeadership). What raft promises of a Ready's messages does not
// say that it sends nothing else.
func deliverable(m *pb.Message) bool {
	switch m.GetType() {
	case pb.MsgProp:
	case pb.MsgReadIndex:
		if m.GetTerm() != 0 {
			return false
		}
	case pb.MsgApp, pb.MsgAppResp, pb.MsgVoteResp, pb.MsgReadIndexResp:
		if m.GetTerm() == 0 {
			return false
		}
	case pb.MsgTimeoutNow:
		if m.GetTerm() == 0 || m.Entries != nil {
			return false
		}
	case pb.MsgSnap:
		if m.GetTerm() == 0 || m.Snapshot == nil || m.Snapshot.GetMetadata().GetIndex() >= maxIndex {
			return false
		}
	case pb.MsgVote, pb.MsgHeartbeat, pb.MsgHeartbeatResp:
		if m.GetTerm() == 0 {
			return false
		}
		return m.GetFrom() != 0 && m.GetFrom() != m.GetTo()
	default:
		return false
	}
	return m.GetFrom() != 0 && m.GetFrom() != m.GetTo() && m.Context == nil
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

// deliver passes the deliverable messages to their targets among peers, each as a fresh
// message (the wire's copy; the receiver may adopt it), and a MsgTimeoutNow only while tr has one
// left; a message to an unknown node is dropped, as is the error of Step.
func deliver(peers map[uint64]raft.Node, tr *transfers, ms []*pb.Message) {
	for _, m := range ms {
		if !deliverable(m) {
			continue
		}
		nd, ok := peers[m.GetTo()]
		if !ok {
			continue
		}
		if m.GetType() == pb.MsgTimeoutNow && !tr.take() {
			continue
		}
		// the wire's copy: a fresh message, its scalar cells shared (raft never writes them),
		// its entries slice its own (the receiver may adopt it), its snapshot a clone (the
		// receiver writes a snapshot's unset fields, pb.EnsureSnapshot), no responses (a
		// deliverable message carries none); stepped instead of raft's own object, which raft
		// still reads after handing it out (issues/nonissues/raft-ready-messages-read-after-handout.md)
		var sn *pb.Snapshot
		if m.Snapshot != nil {
			sn = proto.Clone(m.Snapshot).(*pb.Snapshot)
		}
		c := &pb.Message{
			Type: m.Type, To: m.To, From: m.From, Term: m.Term, LogTerm: m.LogTerm,
			Index: m.Index, Entries: append([]*pb.Entry(nil), m.Entries...), Commit: m.Commit,
			Vote: m.Vote, Reject: m.Reject, RejectHint: m.RejectHint, Context: m.Context,
			Snapshot: sn,
		}
		nd.Step(context.Background(), c)
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

// StartCluster starts a cluster of the given voters connected in process: a replica of the
// store on a raft node of each, with its storage, the transport between them and a node's
// ticks. It returns the replicas, in the order of voters.
func StartCluster(voters []uint64) []*KV {
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
			// a leader that a configuration change removes steps down
			StepDownOnRemoval: true,
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	send := func(ms []*pb.Message) {
		deliver(peers, tr, ms)
	}
	var kvs []*KV
	for _, id := range voters {
		kvs = append(kvs, New(id, peers[id], storages[id], send))
		go tick(peers[id])
	}
	return kvs
}
