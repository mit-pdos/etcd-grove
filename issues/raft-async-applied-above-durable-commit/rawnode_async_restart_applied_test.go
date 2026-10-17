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
// WITHOUT WARRANTIES OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package raft

import (
	"fmt"
	"strings"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// asyncCluster drives three RawNodes with AsyncStorageWrites, routing messages
// by hand. A node's append thread can be stalled: its MsgStorageAppends are
// then held back and never reach its MemoryStorage (a slow disk, then a crash),
// while its apply thread keeps going (doc.go: "Messages to different targets
// can be processed in any order").
type asyncCluster struct {
	t       *testing.T
	rns     map[uint64]*RawNode
	stors   map[uint64]*MemoryStorage
	applied map[uint64]uint64
	stalled map[uint64]bool
	net     []*pb.Message
}

func asyncConfig(id uint64, s Storage, applied uint64) *Config {
	return &Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: s, Applied: applied,
		MaxSizePerMsg: noLimit, MaxInflightMsgs: 256, AsyncStorageWrites: true}
}

func newAsyncCluster(t *testing.T) *asyncCluster {
	c := &asyncCluster{t: t, rns: map[uint64]*RawNode{}, stors: map[uint64]*MemoryStorage{},
		applied: map[uint64]uint64{}, stalled: map[uint64]bool{}}
	for id := uint64(1); id <= 3; id++ {
		s := NewMemoryStorage()
		if err := s.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
			Index: new(uint64(10)), Term: new(uint64(1)),
			ConfState: &pb.ConfState{Voters: []uint64{1, 2, 3}}}}); err != nil {
			t.Fatal(err)
		}
		rn, err := NewRawNode(asyncConfig(id, s, 10))
		if err != nil {
			t.Fatal(err)
		}
		c.rns[id], c.stors[id], c.applied[id] = rn, s, 10
	}
	return c
}

func (c *asyncCluster) persist(id uint64, m *pb.Message) {
	s := c.stors[id]
	if m.GetSnapshot() != nil {
		if err := s.ApplySnapshot(m.GetSnapshot()); err != nil {
			c.t.Fatal(err)
		}
	}
	if err := s.Append(m.GetEntries()); err != nil {
		c.t.Fatal(err)
	}
	if m.Term != nil || m.Vote != nil || m.Commit != nil {
		if err := s.SetHardState(&pb.HardState{Term: new(m.GetTerm()), Vote: new(m.GetVote()),
			Commit: new(m.GetCommit())}); err != nil {
			c.t.Fatal(err)
		}
	}
	c.net = append(c.net, m.GetResponses()...)
}

func (c *asyncCluster) step() bool {
	progress := false
	for id := uint64(1); id <= 3; id++ {
		rn := c.rns[id]
		if !rn.HasReady() {
			continue
		}
		progress = true
		for _, m := range rn.Ready().Messages {
			switch m.GetTo() {
			case LocalAppendThread:
				if !c.stalled[id] {
					c.persist(id, m)
				}
			case LocalApplyThread:
				for _, e := range m.GetEntries() {
					c.applied[id] = e.GetIndex()
				}
				c.net = append(c.net, m.GetResponses()...)
			default:
				c.net = append(c.net, m)
			}
		}
	}
	msgs := c.net
	c.net = nil
	for _, m := range msgs {
		progress = true
		if err := c.rns[m.GetTo()].Step(m); err != nil && err != ErrStepPeerNotFound {
			c.t.Fatal(err)
		}
	}
	return progress
}

func (c *asyncCluster) stabilize() {
	for i := 0; c.step(); i++ {
		if i > 1000 {
			c.t.Fatal("no quiescence")
		}
	}
}

// TestAsyncStorageWritesRestartAppliedAboveDurableCommit: with
// AsyncStorageWrites, the apply thread may apply an entry before the append
// thread has persisted the HardState that commits it. Restarting the node with
// Config.Applied set to the state machine's applied index (as Config.Applied's
// documentation suggests) then panics in NewRawNode: Applied is above the
// durable commit index.
func TestAsyncStorageWritesRestartAppliedAboveDurableCommit(t *testing.T) {
	c := newAsyncCluster(t)
	if err := c.rns[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if err := c.rns[1].Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	// Run until node 1's log durably holds the new entry, then stall its disk.
	for i := 0; i < 100; i++ {
		if last, _ := c.stors[1].LastIndex(); last >= 12 {
			break
		}
		c.step()
	}
	c.stalled[1] = true
	c.stabilize()
	last, _ := c.stors[1].LastIndex()
	hs, _, _ := c.stors[1].InitialState()
	t.Logf("node 1: applied %d; durable last index %d, durable commit %d", c.applied[1], last, hs.GetCommit())
	if c.applied[1] <= hs.GetCommit() || c.applied[1] > last {
		t.Fatalf("applied %d: not in (durable commit %d, durable last %d]", c.applied[1], hs.GetCommit(), last)
	}
	msg := func() (msg string) {
		defer func() {
			if r := recover(); r != nil {
				msg = fmt.Sprint(r)
			}
		}()
		if _, err := NewRawNode(asyncConfig(1, c.stors[1], c.applied[1])); err != nil {
			return "error: " + err.Error()
		}
		return ""
	}()
	t.Logf("restart with Applied=%d: %q", c.applied[1], msg)
	if !strings.Contains(msg, "out of range") {
		t.Fatalf("restart did not panic: %q", msg)
	}
}
