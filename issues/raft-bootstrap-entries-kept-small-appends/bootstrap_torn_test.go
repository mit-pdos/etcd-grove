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

package raft

import (
	"fmt"
	"math/rand"
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// tornCluster is k RawNodes on MemoryStorages, bootstrapped as etcd bootstraps a
// new cluster (raft.StartNode(cfg, peers) on an empty storage: Bootstrap), each
// Ready handled as doc.go describes (persist the snapshot, HardState and
// Entries; send the Messages; apply the CommittedEntries, conf changes
// included; Advance). A member may crash while persisting a Ready's entries,
// keeping any prefix of them and nothing else of the Ready (a torn WAL Save:
// entry records written, state record lost), or before persisting anything, and
// restarts as etcd restarts (raft.RestartNode: NewRawNode from its storage).
type tornCluster struct {
	t       *testing.T
	rng     *rand.Rand
	k       int
	maxSize uint64
	ms      map[uint64]*tornMember
	net     []*pb.Message
	side    map[uint64]int
	// every committed index's entry, over all members
	committed map[uint64]string
	tornFirst map[uint64]int // member -> kept prefix of its first Ready if it crashed in it (-1: it did not)
	crashes   bool
}

type tornMember struct {
	rn      *RawNode
	s       *MemoryStorage
	readies int // Readies handled or crashed in, since the member's bootstrap
}

func (c *tornCluster) config(id uint64, s *MemoryStorage) *Config {
	// etcd's raftConfig (server/etcdserver/bootstrap.go), with a short
	// election timeout.
	return &Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         s,
		MaxSizePerMsg:   c.maxSize,
		MaxInflightMsgs: 4096 / 8,
		CheckQuorum:     true,
		PreVote:         true,
	}
}

func newTornCluster(t *testing.T, k int, maxSize uint64, seed int64) *tornCluster {
	c := &tornCluster{
		t: t, rng: rand.New(rand.NewSource(seed)), k: k, maxSize: maxSize,
		ms: map[uint64]*tornMember{}, side: map[uint64]int{},
		committed: map[uint64]string{}, tornFirst: map[uint64]int{},
	}
	var peers []Peer
	for id := uint64(1); id <= uint64(k); id++ {
		// etcd's peer context: the member's JSON (a few hundred bytes).
		peers = append(peers, Peer{ID: id, Context: []byte(fmt.Sprintf(`{"id":%d,"peerURLs":["http://10.0.0.%d:2380"],"name":"m%d"}`, id, id, id))})
	}
	for id := uint64(1); id <= uint64(k); id++ {
		s := NewMemoryStorage()
		rn, err := NewRawNode(c.config(id, s))
		if err != nil {
			t.Fatal(err)
		}
		if err := rn.Bootstrap(peers); err != nil {
			t.Fatal(err)
		}
		c.ms[id] = &tornMember{rn: rn, s: s}
		c.tornFirst[id] = -1
	}
	return c
}

func (c *tornCluster) restart(id uint64) {
	m := c.ms[id]
	rn, err := NewRawNode(c.config(id, m.s))
	if err != nil {
		c.t.Fatal(err)
	}
	m.rn = rn
}

// handleReady handles member id's Ready, or crashes in it. tornFirst: the
// member's first Ready is torn (member 1's, in the tests).
func (c *tornCluster) handleReady(id uint64, tornFirst bool) {
	m := c.ms[id]
	if !m.rn.HasReady() {
		return
	}
	rd := m.rn.Ready()
	m.readies++
	first := m.readies == 1
	if len(rd.Entries) > 0 && IsEmptySnap(rd.Snapshot) &&
		((first && tornFirst) || (c.crashes && c.rng.Intn(20) == 0)) {
		// A crash in the middle of the WAL's Save: a prefix of the entry
		// records is durable, the state record (HardState) is not; nothing
		// after step 1 happens.
		j := c.rng.Intn(len(rd.Entries) + 1)
		if first {
			c.tornFirst[id] = j
		}
		if j > 0 {
			if err := m.s.Append(rd.Entries[:j]); err != nil {
				c.t.Fatal(err)
			}
		}
		c.restart(id)
		return
	}
	if c.crashes && c.rng.Intn(40) == 0 {
		// A crash before the Ready's Save.
		if first {
			c.tornFirst[id] = 0
		}
		c.restart(id)
		return
	}
	if !IsEmptySnap(rd.Snapshot) {
		if err := m.s.ApplySnapshot(rd.Snapshot); err != nil {
			c.t.Fatal(err)
		}
	}
	if !IsEmptyHardState(rd.HardState) {
		if err := m.s.SetHardState(rd.HardState); err != nil {
			c.t.Fatal(err)
		}
	}
	if err := m.s.Append(rd.Entries); err != nil {
		c.t.Fatal(err)
	}
	c.net = append(c.net, rd.Messages...)
	for _, e := range rd.CommittedEntries {
		d := DescribeEntry(e, nil)
		if old, ok := c.committed[e.GetIndex()]; ok && old != d {
			c.t.Fatalf("index %d committed with two entries: %s and %s (member %d; torn first Readies %v)",
				e.GetIndex(), old, d, id, c.tornFirst)
		}
		c.committed[e.GetIndex()] = d
		if e.GetType() == pb.EntryConfChange {
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				c.t.Fatal(err)
			}
			m.rn.ApplyConfChange(cc)
		}
	}
	m.rn.Advance(rd)
	if c.crashes && c.rng.Intn(40) == 0 {
		// A crash after the Ready: everything persisted.
		c.restart(id)
	}
}

func (c *tornCluster) deliver(i int) {
	msg := c.net[i]
	c.net = append(c.net[:i], c.net[i+1:]...)
	if c.side[msg.GetFrom()] != c.side[msg.GetTo()] {
		return
	}
	_ = c.ms[msg.GetTo()].rn.Step(msg)
}

func (c *tornCluster) step(tornFirst map[uint64]bool) {
	ids := uint64(c.rng.Intn(c.k) + 1)
	switch r := c.rng.Intn(100); {
	case r < 15:
		c.ms[ids].rn.Tick()
	case r < 45:
		c.handleReady(ids, tornFirst[ids])
	case r < 85:
		if len(c.net) > 0 {
			c.deliver(c.rng.Intn(len(c.net)))
		}
	case r < 92:
		if len(c.net) > 0 {
			i := c.rng.Intn(len(c.net))
			c.net = append(c.net[:i], c.net[i+1:]...)
		}
	case r < 94:
		// A new partition: each member on a random side.
		for id := uint64(1); id <= uint64(c.k); id++ {
			c.side[id] = c.rng.Intn(2)
		}
	case r < 96:
		c.side = map[uint64]int{}
	case r < 98:
		_ = c.ms[ids].rn.Campaign()
	default:
		_ = c.ms[ids].rn.Propose([]byte(fmt.Sprintf("p%d", c.rng.Intn(1000))))
	}
}

// heal stops crashes and partitions, then runs until every member is a voter
// of the whole configuration and all agree on a committed index past the
// bootstrap log.
func (c *tornCluster) heal() bool {
	c.crashes = false
	c.side = map[uint64]int{}
	for round := 0; round < 400; round++ {
		for id := uint64(1); id <= uint64(c.k); id++ {
			c.ms[id].rn.Tick()
		}
		for busy := true; busy; {
			busy = false
			for id := uint64(1); id <= uint64(c.k); id++ {
				if c.ms[id].rn.HasReady() {
					busy = true
					c.handleReady(id, false)
				}
			}
			for len(c.net) > 0 {
				busy = true
				c.deliver(0)
			}
		}
		if round%50 == 49 {
			for id := uint64(1); id <= uint64(c.k); id++ {
				if c.ms[id].rn.raft.state == StateLeader {
					_ = c.ms[id].rn.Propose([]byte("heal"))
				}
			}
		}
		ok := true
		var commit uint64
		for id := uint64(1); id <= uint64(c.k); id++ {
			r := c.ms[id].rn.raft
			if _, in := r.trk.Voters.IDs()[id]; !in || len(r.trk.Voters.IDs()) != c.k {
				ok = false
			}
			if id == 1 {
				commit = r.raftLog.committed
			} else if r.raftLog.committed != commit {
				ok = false
			}
		}
		if ok && commit > uint64(c.k) {
			return true
		}
	}
	return false
}

func runBootstrapTorn(t *testing.T, k int, maxSize uint64, crashes bool, seeds int) {
	lost := 0
	defer func() {
		t.Logf("%d of %d runs: every member lost its bootstrap Ready (rejoin not checked)", lost, seeds)
	}()
	for seed := 0; seed < seeds; seed++ {
		c := newTornCluster(t, k, maxSize, int64(seed))
		c.crashes = crashes
		tornFirst := map[uint64]bool{1: true}
		for i := 0; i < 3000; i++ {
			c.step(tornFirst)
		}
		lostAll := true
		for id := uint64(1); id <= uint64(k); id++ {
			if c.tornFirst[id] < 0 {
				lostAll = false
			}
		}
		if lostAll {
			// No member persisted the bootstrap configuration: none can
			// campaign, ever (liveness, not checked).
			lost++
			continue
		}
		if !c.heal() {
			for id := uint64(1); id <= uint64(k); id++ {
				r := c.ms[id].rn.raft
				hs, cs, _ := c.ms[id].s.InitialState()
				t.Logf("member %d: state %v term %d lead %d voters %v committed %d applied %d last %d; stored %v %v", id, r.state, r.Term, r.lead, r.trk.Voters, r.raftLog.committed, r.raftLog.applied, r.raftLog.lastIndex(), hs, cs)
			}
			t.Fatalf("seed %d: members did not rejoin (torn first Readies %v)", seed, c.tornFirst)
		}
	}
}

// TestBootstrapTornFirstReady: member 1's first Ready (the bootstrap log of
// conf changes, with HardState{Term: 1, Commit: k}) is torn: some prefix of its
// entries is kept, the HardState is lost, and member 1 restarts from its
// storage (commit 0, an empty configuration). Under random schedules of
// ticks, message deliveries and drops, partitions, campaigns and proposals,
// no index is committed with two different entries, and member 1 rejoins as a
// voter of the whole configuration once the network heals. (With k = 1 member
// 1 is the only member and cannot rejoin: a single-member cluster whose
// bootstrap Save is torn has no voter left; liveness, not checked.)
func TestBootstrapTornFirstReady(t *testing.T) {
	for _, k := range []int{1, 3, 5} {
		t.Run(fmt.Sprintf("k=%d", k), func(t *testing.T) {
			runBootstrapTorn(t, k, 1024*1024, false, 300)
		})
	}
}

// TestBootstrapTornAnyReady: as TestBootstrapTornFirstReady, and every member
// may also crash in any later Ready, before persisting it, after it, or in the
// middle of its entries (a torn Save, which in a cluster that never changes
// its membership after the bootstrap can hold conf changes only when it holds
// bootstrap entries the member's own torn bootstrap lost).
func TestBootstrapTornAnyReady(t *testing.T) {
	for _, k := range []int{1, 3, 5} {
		t.Run(fmt.Sprintf("k=%d", k), func(t *testing.T) {
			runBootstrapTorn(t, k, 1024*1024, true, 300)
		})
	}
}
