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

// Reproduction of issues/etcd-merged-snapshot-stale-term.md at raft level.
//
// Five RawNodes (1 = A, 2 = B, 3 = C, 4 = D, 5 = E) run the real raft code.
// Node 1 is driven the way etcd's raftNode and applyAll drive it
// (server/etcdserver/raft.go, server.go at 8a24be2a3):
//
//   - each Ready becomes one apply job, holding its CommittedEntries;
//   - MsgSnap messages are not sent but pushed onto msgSnapC, in the reverse
//     order of rd.Messages (processMessages);
//   - a Ready is saved and advanced only when the test says so (a slow WAL
//     fsync in raftNode's Save), and node.run keeps stepping incoming
//     messages meanwhile (node.go: recvc is served while advancec is armed);
//   - after its Ready is saved and advanced, a job applies its entries
//     (appliedi, appliedt) and takes at most one message off msgSnapC, which
//     it sends with Snapshot replaced by (appliedi, appliedt, confState) and
//     Term and From unchanged (createMergedSnapshotMessage).
//
// The test ends with node 5 at raft term 1 holding a log whose last entry
// has term 2. With checkTerm (the fix: merge only when the latest
// HardState.Term the raft goroutine saw equals m.Term), the message is
// dropped and node 5 stays consistent.

import (
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

type msSim struct {
	t     *testing.T
	nodes map[uint64]*RawNode
	st    map[uint64]*MemoryStorage
	queue []*pb.Message
	// cut[{from,to}]: messages from -> to are dropped.
	cut map[[2]uint64]bool

	// etcd's pipeline on node 1
	pending   *Ready // handed out, not yet saved/advanced
	jobs      [][]*pb.Entry
	msgSnapC  []*pb.Message
	appliedi  uint64
	appliedt  uint64
	islead    bool   // raftNode's islead, from the latest SoftState
	hsTerm    uint64 // latest rd.HardState.Term seen by the raft goroutine
	checkTerm bool
	merged    []*pb.Message // merged messages sent by node 1
}

func newMsSim(t *testing.T, checkTerm bool) *msSim {
	s := &msSim{t: t, nodes: map[uint64]*RawNode{}, st: map[uint64]*MemoryStorage{},
		cut: map[[2]uint64]bool{}, checkTerm: checkTerm}
	for id := uint64(1); id <= 5; id++ {
		st := newTestMemoryStorage(withPeers(1, 2, 3, 4, 5))
		cfg := newTestConfig(id, 10, 1, st)
		cfg.PreVote = true
		cfg.CheckQuorum = true
		rn, err := NewRawNode(cfg)
		require.NoError(t, err)
		s.nodes[id], s.st[id] = rn, st
	}
	return s
}

func (s *msSim) send(ms []*pb.Message) {
	for _, m := range ms {
		s.queue = append(s.queue, m)
	}
}

// ready handles a full Ready of a plain node (2..5): persist, send, advance.
func (s *msSim) ready(id uint64) {
	rn := s.nodes[id]
	for rn.HasReady() {
		rd := rn.Ready()
		st := s.st[id]
		if !IsEmptySnap(rd.Snapshot) {
			require.NoError(s.t, st.ApplySnapshot(rd.Snapshot))
		}
		require.NoError(s.t, st.Append(rd.Entries))
		if !IsEmptyHardState(rd.HardState) {
			require.NoError(s.t, st.SetHardState(rd.HardState))
		}
		s.send(rd.Messages)
		rn.Advance(rd)
	}
}

// aBegin hands out node 1's next Ready (raftNode: up to the Save).
func (s *msSim) aBegin() bool {
	rn := s.nodes[1]
	if s.pending != nil || !rn.HasReady() {
		return false
	}
	rd := rn.Ready()
	s.pending = &rd
	if !IsEmptyHardState(rd.HardState) {
		s.hsTerm = rd.HardState.GetTerm()
	}
	if rd.SoftState != nil {
		s.islead = rd.RaftState == StateLeader
	}
	s.jobs = append(s.jobs, rd.CommittedEntries)
	if s.islead {
		// leader: processMessages and Send before the Save
		s.processMessages(rd.Messages)
	}
	return true
}

func (s *msSim) processMessages(ms []*pb.Message) {
	var out []*pb.Message
	for i := len(ms) - 1; i >= 0; i-- {
		if ms[i].GetType() == pb.MsgSnap {
			s.msgSnapC = append(s.msgSnapC, ms[i])
			continue
		}
		out = append(out, ms[i])
	}
	s.send(out)
}

// aFinish saves and advances node 1's pending Ready, then runs its job.
func (s *msSim) aFinish() {
	rd := *s.pending
	st := s.st[1]
	if !IsEmptySnap(rd.Snapshot) {
		require.NoError(s.t, st.ApplySnapshot(rd.Snapshot))
	}
	if !IsEmptyHardState(rd.HardState) {
		require.NoError(s.t, st.SetHardState(rd.HardState))
	}
	if !s.islead {
		// follower: processMessages and Send after the Save
		s.processMessages(rd.Messages)
	}
	require.NoError(s.t, st.Append(rd.Entries))
	s.nodes[1].Advance(rd)
	s.pending = nil
	s.runJob()
}

func (s *msSim) runJob() {
	ents := s.jobs[0]
	s.jobs = s.jobs[1:]
	for _, e := range ents {
		s.appliedi, s.appliedt = e.GetIndex(), e.GetTerm()
	}
	if len(s.msgSnapC) == 0 {
		return
	}
	m := s.msgSnapC[0]
	s.msgSnapC = s.msgSnapC[1:]
	if s.checkTerm && s.hsTerm != m.GetTerm() {
		return // dropped: raft is no longer at m.Term
	}
	merged := proto.Clone(m).(*pb.Message)
	merged.Snapshot = &pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index:     new(s.appliedi),
		Term:      new(s.appliedt),
		ConfState: &pb.ConfState{Voters: []uint64{1, 2, 3, 4, 5}},
	}}
	s.merged = append(s.merged, merged)
	s.send([]*pb.Message{merged})
}

// deliver delivers queued messages until none is left. Node 1 only steps
// them; its Readys are handled by aBegin/aFinish.
func (s *msSim) deliver() {
	for len(s.queue) > 0 {
		m := s.queue[0]
		s.queue = s.queue[1:]
		from, to := m.GetFrom(), m.GetTo()
		if s.cut[[2]uint64{from, to}] {
			s.nodes[from].ReportUnreachable(to) // rafthttp reports a failed send
			continue
		}
		_ = s.nodes[to].Step(m)
		if to != 1 {
			s.ready(to)
		}
	}
}

// settle runs everything, node 1 included, until quiet.
func (s *msSim) settle() {
	for i := 0; i < 100; i++ {
		for id := uint64(2); id <= 5; id++ {
			s.ready(id)
		}
		progressed := false
		for s.aBegin() {
			s.aFinish()
			progressed = true
		}
		if len(s.queue) == 0 && !progressed {
			return
		}
		s.deliver()
	}
	s.t.Fatal("did not settle")
}

func (s *msSim) isolate(id uint64, from ...uint64) {
	for _, o := range from {
		s.cut[[2]uint64{id, o}] = true
		s.cut[[2]uint64{o, id}] = true
	}
}

func (s *msSim) heal() { s.cut = map[[2]uint64]bool{} }

func runMergedSnapshotScenario(t *testing.T, checkTerm bool) *msSim {
	s := newMsSim(t, checkTerm)
	a, e := s.nodes[1], s.nodes[5]

	// A (1) is leader at term 1.
	require.NoError(t, a.Campaign())
	s.settle()
	require.Equal(t, StateLeader, a.raft.state)
	require.Equal(t, uint64(1), a.raft.Term)

	// D (4) and E (5) are cut off; A commits entries with B and C and
	// compacts its raft log past D's and E's logs (etcd's
	// snapshotIfNeededAndCompactRaftLog).
	s.isolate(4, 1, 2, 3, 5)
	s.isolate(5, 1, 2, 3, 4)
	for i := 0; i < 20; i++ {
		require.NoError(t, a.Propose([]byte("x")))
		s.settle()
	}
	ai := s.appliedi
	_, err := s.st[1].CreateSnapshot(ai, &pb.ConfState{Voters: []uint64{1, 2, 3, 4, 5}}, nil)
	require.NoError(t, err)
	require.NoError(t, s.st[1].Compact(ai-2))
	li4, _ := s.st[4].LastIndex()
	li5, _ := s.st[5].LastIndex()
	require.Less(t, li4, ai-2)
	require.Less(t, li5, ai-2)

	// D reconnects to everyone; E only to A (E stays cut off from B, C, D).
	s.heal()
	s.isolate(5, 2, 3, 4)
	// Deterministic timeouts: B times out first.
	for id := uint64(2); id <= 5; id++ {
		setRandomizedElectionTimeout(s.nodes[id].raft, 19)
	}
	setRandomizedElectionTimeout(s.nodes[2].raft, 10)

	// Ready k-1: A's heartbeat. Its Save then stalls (slow fsync): A's
	// raftNode loop is blocked, so A neither ticks nor emits a Ready, but
	// node.run still steps incoming messages.
	a.Tick()
	require.True(t, s.aBegin())
	// The heartbeat responses reach A, E's first: A, still leader at term 1,
	// finds D's and E's next entries compacted and creates MsgSnap to E,
	// then to D (stamped with term 1).
	s.queue = sortFirst(s.queue, 5)
	s.deliver()
	require.Len(t, a.raft.msgs, 2)
	for _, m := range a.raft.msgs {
		require.Equal(t, pb.MsgSnap, m.GetType())
		require.Equal(t, uint64(1), m.GetTerm())
	}

	// B, C, D hear nothing from A for an election timeout; B wins term 2
	// (pre-vote) with C and D. E, also hearing nothing, pre-votes at A only,
	// which ignores it (in lease), so E stays at term 1.
	for i := 0; i < 15; i++ {
		for id := uint64(2); id <= 5; id++ {
			s.nodes[id].Tick()
			s.ready(id)
		}
		s.deliver()
	}
	require.Equal(t, StateLeader, s.nodes[2].raft.state)
	require.Equal(t, uint64(2), s.nodes[2].raft.Term)
	require.Equal(t, uint64(1), e.raft.Term)
	// A has stepped B's term-2 append: a follower at term 2, its reply queued.
	require.Equal(t, StateFollower, a.raft.state)
	require.Equal(t, uint64(2), a.raft.Term)
	// B has committed its term-2 entry with C and D.
	bCommit := s.nodes[2].raft.raftLog.committed
	require.Equal(t, uint64(2), s.nodes[2].raft.raftLog.lastEntryID().term)

	// The fsync returns: job k-1 (no message yet). Ready k: A is a follower
	// at term 2; its messages carry the two term-1 MsgSnaps (pushed onto
	// msgSnapC, D's first) and its reply to B. Job k merges D's with A's
	// term-1 content; D is at term 2 and ignores it.
	s.aFinish()
	require.True(t, s.aBegin())
	require.Equal(t, uint64(2), s.hsTerm)
	s.aFinish()
	require.Len(t, s.msgSnapC, 1)
	require.Equal(t, uint64(5), s.msgSnapC[0].GetTo())

	// B gets A's reply and sends it the commit. Ready k+1 commits B's
	// term-2 entry; job k+1 applies it and merges E's term-1 message with it.
	s.deliver()
	require.True(t, s.aBegin())
	s.aFinish()
	require.Equal(t, uint64(2), s.appliedt)
	require.GreaterOrEqual(t, s.appliedi, bCommit)
	require.Empty(t, s.msgSnapC)
	s.deliver()
	return s
}

func sortFirst(ms []*pb.Message, from uint64) []*pb.Message {
	var first, rest []*pb.Message
	for _, m := range ms {
		if m.GetFrom() == from {
			first = append(first, m)
		} else {
			rest = append(rest, m)
		}
	}
	return append(first, rest...)
}

func TestMergedSnapshotStaleTerm(t *testing.T) {
	s := runMergedSnapshotScenario(t, false)
	e := s.nodes[5]

	// The merged message E received: term 1 (A's, when it made the MsgSnap),
	// content (appliedi, 2).
	last := s.merged[len(s.merged)-1]
	require.Equal(t, uint64(5), last.GetTo())
	require.Equal(t, uint64(1), last.GetTerm())
	require.Equal(t, uint64(2), last.GetSnapshot().GetMetadata().GetTerm())

	// E accepted it at term 1: its log now ends with a term-2 entry while its
	// term is 1, against Raft's "currentTerm >= last log term".
	require.Equal(t, uint64(1), e.raft.Term)
	require.Equal(t, s.appliedi, e.raft.raftLog.lastIndex())
	lastTerm := e.raft.raftLog.lastEntryID().term
	require.Equal(t, uint64(2), lastTerm)
	st := e.Status()
	t.Logf("E: Term=%d lastIndex=%d lastTerm=%d (state %s)", st.GetTerm(), e.raft.raftLog.lastIndex(), lastTerm, st.RaftState)
	stTerm, err := s.st[5].Term(s.appliedi)
	require.NoError(t, err)
	require.Greater(t, stTerm, st.GetTerm(), "E's stored log ends at a term above its raft term")
}

func TestMergedSnapshotStaleTermFixed(t *testing.T) {
	s := runMergedSnapshotScenario(t, true)
	e := s.nodes[5]
	for _, m := range s.merged {
		require.NotEqual(t, uint64(5), m.GetTo(), "the stale message is dropped")
	}
	require.Equal(t, uint64(1), e.raft.Term)
	require.LessOrEqual(t, e.raft.raftLog.lastEntryID().term, e.raft.Term)
}
