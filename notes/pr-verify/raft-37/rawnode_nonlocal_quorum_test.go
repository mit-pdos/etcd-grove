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

// nlqCluster drives three RawNodes with AsyncStorageWrites and
// AsyncStorageWritesNonLocalQuorum, routing messages by hand. A node's append
// thread can be stalled: its MsgStorageAppends are then held back, never
// reaching its MemoryStorage (a disk stall followed by a crash).
type nlqCluster struct {
	t       *testing.T
	rns     map[uint64]*RawNode
	stors   map[uint64]*MemoryStorage
	applied map[uint64]uint64
	stalled map[uint64]bool
	held    map[uint64][]pb.Message
	net     []pb.Message
}

func nlqConfig(id uint64, s Storage, applied uint64) *Config {
	return &Config{
		ID:                               id,
		ElectionTick:                     10,
		HeartbeatTick:                    1,
		Storage:                          s,
		Applied:                          applied,
		MaxSizePerMsg:                    noLimit,
		MaxInflightMsgs:                  256,
		AsyncStorageWrites:               true,
		AsyncStorageWritesNonLocalQuorum: true,
	}
}

func newNLQCluster(t *testing.T) *nlqCluster {
	c := &nlqCluster{t: t, rns: map[uint64]*RawNode{}, stors: map[uint64]*MemoryStorage{},
		applied: map[uint64]uint64{}, stalled: map[uint64]bool{}, held: map[uint64][]pb.Message{}}
	for id := uint64(1); id <= 3; id++ {
		s := NewMemoryStorage()
		snap := pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1,
			ConfState: pb.ConfState{Voters: []uint64{1, 2, 3}}}}
		if err := s.ApplySnapshot(snap); err != nil {
			t.Fatal(err)
		}
		rn, err := NewRawNode(nlqConfig(id, s, 10))
		if err != nil {
			t.Fatal(err)
		}
		c.rns[id], c.stors[id], c.applied[id] = rn, s, 10
	}
	return c
}

func (c *nlqCluster) persist(id uint64, m pb.Message) {
	s := c.stors[id]
	if m.Snapshot != nil {
		if err := s.ApplySnapshot(*m.Snapshot); err != nil {
			c.t.Fatal(err)
		}
	}
	if err := s.Append(m.Entries); err != nil {
		c.t.Fatal(err)
	}
	if m.Term != 0 || m.Vote != 0 || m.Commit != 0 {
		if err := s.SetHardState(pb.HardState{Term: m.Term, Vote: m.Vote, Commit: m.Commit}); err != nil {
			c.t.Fatal(err)
		}
	}
	c.net = append(c.net, m.Responses...)
}

// step runs one round: every node's Ready, then every queued message. It
// reports whether anything happened.
func (c *nlqCluster) step() bool {
	progress := false
	for id := uint64(1); id <= 3; id++ {
		rn := c.rns[id]
		if !rn.HasReady() {
			continue
		}
		progress = true
		rd := rn.Ready()
		for _, m := range rd.Messages {
			switch m.To {
			case LocalAppendThread:
				if c.stalled[id] {
					c.held[id] = append(c.held[id], m)
				} else {
					c.persist(id, m)
				}
			case LocalApplyThread:
				for _, e := range m.Entries {
					c.applied[id] = e.Index
				}
				c.net = append(c.net, m.Responses...)
			default:
				c.net = append(c.net, m)
			}
		}
	}
	msgs := c.net
	c.net = nil
	for _, m := range msgs {
		progress = true
		if err := c.rns[m.To].Step(m); err != nil && err != ErrStepPeerNotFound {
			c.t.Fatal(err)
		}
	}
	return progress
}

func (c *nlqCluster) stabilize() {
	for i := 0; c.step(); i++ {
		if i > 1000 {
			c.t.Fatal("no quiescence")
		}
	}
}

// TestNonLocalQuorumRestartAboveDurableLog shows that with
// AsyncStorageWritesNonLocalQuorum a node can apply an entry that never
// reached its own durable log. An application that records its applied index
// with its state machine (as Config.Applied asks it to on restart) then cannot
// restart the node: NewRawNode panics, since Applied is above the commit index
// and the last index of the node's durable log. Restarting with a lower Applied
// re-delivers entries the state machine already applied. (Plain
// AsyncStorageWrites already lets the applied index pass the durable commit,
// with the same panic; what the option adds is applied above the durable last
// index: the state machine holds an entry the node's own disk does not.)
func TestNonLocalQuorumRestartAboveDurableLog(t *testing.T) {
	c := newNLQCluster(t)
	if err := c.rns[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if st := c.rns[1].raft.state; st != StateLeader {
		t.Fatalf("node 1 is %v, not the leader", st)
	}
	// Node 1's disk stalls; it proposes an entry, which nodes 2 and 3 persist.
	c.stalled[1] = true
	if err := c.rns[1].Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	last, _ := c.stors[1].LastIndex()
	hs, _, _ := c.stors[1].InitialState()
	t.Logf("node 1: applied %d; durable log last index %d, durable commit %d", c.applied[1], last, hs.Commit)
	if c.applied[1] <= last {
		t.Fatalf("node 1 applied %d, not above its durable last index %d", c.applied[1], last)
	}
	// Node 1 crashes before its append thread writes. Restart it from what
	// is durable: its storage, and the state machine's applied index.
	msg := func() (msg string) {
		defer func() {
			if r := recover(); r != nil {
				msg = fmt.Sprint(r)
			}
		}()
		if _, err := NewRawNode(nlqConfig(1, c.stors[1], c.applied[1])); err != nil {
			return "error: " + err.Error()
		}
		return ""
	}()
	t.Logf("restart with Applied=%d: %q", c.applied[1], msg)
	if !strings.Contains(msg, "out of range") {
		t.Fatalf("restart did not panic as expected: %q", msg)
	}
}

// TestNonLocalQuorumFollowerAppliesUnstable shows that the option is not
// confined to the leader, as its documentation says ("on the leader"): a
// follower whose disk stalls applies an entry it holds only in its unstable
// log, once the leader tells it the entry is committed.
func TestNonLocalQuorumFollowerAppliesUnstable(t *testing.T) {
	c := newNLQCluster(t)
	if err := c.rns[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	c.stalled[3] = true
	if err := c.rns[1].Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	last, _ := c.stors[3].LastIndex()
	t.Logf("follower 3: applied %d; durable log last index %d", c.applied[3], last)
	if c.rns[3].raft.state != StateFollower || c.applied[3] <= last {
		t.Fatalf("follower 3 (%v) applied %d, not above its durable last index %d",
			c.rns[3].raft.state, c.applied[3], last)
	}
}
