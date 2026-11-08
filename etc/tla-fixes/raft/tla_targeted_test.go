// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//go:build with_tla

package raft

import (
	"os"
	"path/filepath"
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// Targeted schedules for the mutants random runs rarely reach (etc/tla-fixes/README.md). Each
// only validates its trace: with correct raft every trace is accepted; a mutant that breaks the
// rule the schedule exercises makes TLC reject it. Needs TLA_TOOLS (tla_random_test.go).

type tgCluster struct {
	t        *testing.T
	rec      *rndRecorder
	nodes    map[uint64]*RawNode
	sts      map[uint64]*MemoryStorage
	applied  map[uint64]uint64
	cs       map[uint64]*pb.ConfState
	maxSize  uint64
	inflight []*pb.Message
}

func newTgCluster(t *testing.T, maxSize uint64) *tgCluster {
	c := &tgCluster{t: t, rec: &rndRecorder{}, nodes: map[uint64]*RawNode{}, sts: map[uint64]*MemoryStorage{},
		applied: map[uint64]uint64{}, cs: map[uint64]*pb.ConfState{}, maxSize: maxSize}
	for id := uint64(1); id <= 3; id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(c.config(id, st, 0))
		if err != nil {
			t.Fatal(err)
		}
		if err := rn.Bootstrap([]Peer{{ID: 1}, {ID: 2}, {ID: 3}}); err != nil {
			t.Fatal(err)
		}
		c.nodes[id], c.sts[id] = rn, st
	}
	for id := uint64(1); id <= 3; id++ {
		c.ready(id)
	}
	return c
}

func (c *tgCluster) config(id uint64, st *MemoryStorage, applied uint64) *Config {
	return &Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st, Applied: applied,
		MaxSizePerMsg: c.maxSize, MaxInflightMsgs: 256, TraceLogger: c.rec, Logger: discardLogger}
}

// restart restarts id from its storage, its application having snapshotted what it applied.
func (c *tgCluster) restart(id uint64) {
	if _, err := c.sts[id].CreateSnapshot(c.applied[id], c.cs[id], nil); err != nil {
		c.t.Fatal(err)
	}
	rn, err := NewRawNode(c.config(id, c.sts[id], c.applied[id]))
	if err != nil {
		c.t.Fatal(err)
	}
	c.nodes[id] = rn
}

func (c *tgCluster) ready(id uint64) {
	for c.nodes[id].HasReady() {
		rn, st := c.nodes[id], c.sts[id]
		rd := rn.Ready()
		if err := st.Append(rd.Entries); err != nil {
			c.t.Fatal(err)
		}
		if rd.HardState != nil && !IsEmptyHardState(rd.HardState) {
			if err := st.SetHardState(rd.HardState); err != nil {
				c.t.Fatal(err)
			}
		}
		for _, m := range rd.Messages {
			c.inflight = append(c.inflight, proto.Clone(m).(*pb.Message))
		}
		for _, e := range rd.CommittedEntries {
			if e.GetType() == pb.EntryConfChange {
				cc := &pb.ConfChange{}
				if err := proto.Unmarshal(e.GetData(), cc); err != nil {
					c.t.Fatal(err)
				}
				c.cs[id] = rn.ApplyConfChange(cc)
			}
			c.applied[id] = e.GetIndex()
		}
		rn.Advance(rd)
	}
}

// deliver delivers the first message from -> to of type typ.
func (c *tgCluster) deliver(from, to uint64, typ pb.MessageType) {
	for k, m := range c.inflight {
		if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
			c.inflight = append(c.inflight[:k:k], c.inflight[k+1:]...)
			if err := c.nodes[to].Step(m); err != nil {
				c.t.Fatal(err)
			}
			return
		}
	}
	c.t.Fatalf("no %v %d->%d in flight", typ, from, to)
}

// flush delivers everything in order, handling Readys, dropping the messages drop selects.
func (c *tgCluster) flush(drop func(*pb.Message) bool) {
	for {
		for id := uint64(1); id <= 3; id++ {
			c.ready(id)
		}
		if len(c.inflight) == 0 {
			return
		}
		m := c.inflight[0]
		c.inflight = c.inflight[1:]
		if drop != nil && drop(m) {
			continue
		}
		if err := c.nodes[m.GetTo()].Step(m); err != nil {
			c.t.Fatal(err)
		}
	}
}

func (c *tgCluster) validate() {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		c.t.Skip("TLA_TOOLS not set")
	}
	spec, err := filepath.Abs("tla")
	if err != nil {
		c.t.Fatal(err)
	}
	if msg := validateTrace(c.t, tools, spec, c.rec.lines); msg != "" {
		c.t.Fatalf("rejected: %s", msg)
	}
}

// TestTLATargetedVoteKnownLeader: a follower learns its term's leader from a heartbeat, then the
// leader's own delayed MsgVote of that term arrives (raft refuses it: issues/raft-tla-vote-
// refused-known-leader.md's schedule).
func TestTLATargetedVoteKnownLeader(t *testing.T) {
	c := newTgCluster(t, 4096)
	if err := c.nodes[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.ready(1)
	c.deliver(1, 2, pb.MessageType_MsgVote)
	c.ready(2)
	c.deliver(2, 1, pb.MessageType_MsgVoteResp)
	c.ready(1)
	c.nodes[1].Tick()
	c.ready(1)
	c.deliver(1, 3, pb.MessageType_MsgHeartbeat)
	c.ready(3)
	c.deliver(1, 3, pb.MessageType_MsgVote)
	c.ready(3)
	c.deliver(3, 1, pb.MessageType_MsgVoteResp)
	c.ready(1)
	c.validate()
}

// TestTLATargetedVoteKnownLeaderFromApp: a follower in the leader's term that does not know the
// leader (it restarted) learns it from the leader's MsgApp (raft's stepFollower), then the
// leader's delayed MsgVote of that term arrives.
func TestTLATargetedVoteKnownLeaderFromApp(t *testing.T) {
	c := newTgCluster(t, 4096)
	if err := c.nodes[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.ready(1)
	c.deliver(1, 2, pb.MessageType_MsgVote)
	c.ready(2)
	c.deliver(2, 1, pb.MessageType_MsgVoteResp)
	c.ready(1)
	c.nodes[1].Tick()
	c.ready(1)
	c.deliver(1, 3, pb.MessageType_MsgHeartbeat)
	c.ready(3)
	c.restart(3)
	if s := c.nodes[3].BasicStatus(); s.HardState.GetTerm() != 2 || s.Lead != None {
		t.Fatalf("node 3 restarted: term %d lead %d, want term 2 and no leader", s.HardState.GetTerm(), s.Lead)
	}
	c.deliver(1, 3, pb.MessageType_MsgApp)
	c.ready(3)
	c.deliver(1, 3, pb.MessageType_MsgVote)
	c.ready(3)
	c.deliver(3, 1, pb.MessageType_MsgVoteResp)
	c.ready(1)
	c.validate()
}

// TestTLATargetedResentEntryCommit: a follower holding entries 5..7, its answers lost, gets entry
// 5 again (one entry per MsgApp) with the leader's commit index 7: it commits 5, the last entry
// the request verified, not 7.
func TestTLATargetedResentEntryCommit(t *testing.T) {
	c := newTgCluster(t, 1)
	if err := c.nodes[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.flush(nil)
	for k := 0; k < 3; k++ {
		if err := c.nodes[1].Propose([]byte{byte('a' + k)}); err != nil {
			t.Fatal(err)
		}
	}
	// Node 3's answers are lost, and so is the empty MsgApp that would tell it of the commit.
	lost := func(m *pb.Message) bool {
		return (m.GetFrom() == 3 && m.GetType() == pb.MessageType_MsgAppResp) ||
			(m.GetTo() == 3 && m.GetType() == pb.MessageType_MsgApp && len(m.GetEntries()) == 0)
	}
	c.flush(lost)
	if l3, l1, c3 := c.nodes[3].raft.raftLog.lastIndex(), c.nodes[1].raft.raftLog.lastIndex(), c.nodes[3].raft.raftLog.committed; l3 != l1 || c3 >= l1-1 {
		t.Fatalf("node 3: last index %d commit %d, want the leader's last index %d and a commit below it", l3, c3, l1)
	}
	// The leader stops trusting node 3's progress (as on an unreachable report) and probes it
	// again from its match index.
	c.nodes[1].ReportUnreachable(3)
	c.nodes[1].Tick()
	c.ready(1)
	c.deliver(1, 3, pb.MessageType_MsgHeartbeat)
	c.ready(3)
	c.deliver(3, 1, pb.MessageType_MsgHeartbeatResp)
	c.ready(1)
	c.deliver(1, 3, pb.MessageType_MsgApp)
	c.ready(3)
	c.flush(nil)
	c.validate()
}
