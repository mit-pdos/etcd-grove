// Review tests for etcd-io/etcd#22223 (raft async storage writes).
package etcdserver

import (
	"math"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// sendRecorder records, for every MsgApp handed to the transport, the
// committed index etcd's raftReadyHandler had published at that moment.
type sendRecorder struct {
	nopTransporter
	mu        sync.Mutex
	committed *uint64
	cmu       *sync.Mutex
	seen      []uint64 // etcd committed index when a MsgApp carrying Commit was sent
	commits   []uint64 // the Commit carried
}

func (s *sendRecorder) Send(ms []*raftpb.Message) {
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, m := range ms {
		if m.GetType() == raftpb.MsgApp {
			s.cmu.Lock()
			c := *s.committed
			s.cmu.Unlock()
			s.seen = append(s.seen, c)
			s.commits = append(s.commits, m.GetCommit())
		}
	}
}

func newCommitTrackingHandler(mu *sync.Mutex, committed *uint64) *raftReadyHandler {
	rh := newTestRaftReadyHandler()
	rh.updateCommittedIndex = func(ci uint64) {
		mu.Lock()
		defer mu.Unlock()
		if ci > *committed {
			*committed = ci
		}
	}
	return rh
}

func leaderReady(async bool) raft.Ready {
	entry := &raftpb.Entry{Index: new(uint64(1)), Term: new(uint64(1))}
	msgApp := &raftpb.Message{
		Type: raftpb.MsgApp.Enum(), From: new(uint64(1)), To: new(uint64(2)),
		Term: new(uint64(1)), Index: new(uint64(1)), LogTerm: new(uint64(1)), Commit: new(uint64(1)),
	}
	if !async {
		return raft.Ready{
			SoftState:        &raft.SoftState{Lead: 1, RaftState: raft.StateLeader},
			HardState:        &raftpb.HardState{Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(uint64(1))},
			CommittedEntries: []*raftpb.Entry{entry},
			Messages:         []*raftpb.Message{msgApp},
		}
	}
	appendMsg := &raftpb.Message{
		Type: raftpb.MsgStorageAppend.Enum(), To: new(raft.LocalAppendThread), From: new(uint64(1)),
		Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(uint64(1)),
	}
	applyMsg := &raftpb.Message{
		Type: raftpb.MsgStorageApply.Enum(), To: new(raft.LocalApplyThread), From: new(uint64(1)),
		Entries: []*raftpb.Entry{entry},
		Responses: []*raftpb.Message{{
			Type: raftpb.MsgStorageApplyResp.Enum(), To: new(uint64(1)), From: new(raft.LocalApplyThread),
			Entries: []*raftpb.Entry{entry},
		}},
	}
	// Order as raft's readyWithoutAccept builds it: r.msgs, then the
	// MsgStorageAppend, then the MsgStorageApply.
	return raft.Ready{
		SoftState: &raft.SoftState{Lead: 1, RaftState: raft.StateLeader},
		Messages:  []*raftpb.Message{msgApp, appendMsg, applyMsg},
	}
}

func runLeaderReady(t *testing.T, async bool) (seen, commits []uint64) {
	var mu sync.Mutex
	var committed uint64
	tr := &sendRecorder{committed: &committed, cmu: &mu}
	n := newAsyncReadyNode()
	r := newRaftNode(raftNodeConfig{
		lg:                 zaptest.NewLogger(t),
		Node:               n,
		localID:            1,
		asyncStorageWrites: async,
		isIDRemoved:        func(uint64) bool { return false },
		storage:            mockstorage.NewStorageRecorder(""),
		raftStorage:        raft.NewMemoryStorage(),
		transport:          tr,
	})
	rh := newCommitTrackingHandler(&mu, &committed)
	r.start(rh)
	defer r.stop()
	n.readyc <- leaderReady(async)
	ap := <-r.applyc
	<-ap.raftStorageReadyC
	ap.notifyApplyCompleted()
	deadline := time.After(2 * time.Second)
	for {
		tr.mu.Lock()
		k := len(tr.seen)
		tr.mu.Unlock()
		if k > 0 {
			break
		}
		select {
		case <-deadline:
			t.Fatal("MsgApp never sent")
		case <-time.After(10 * time.Millisecond):
		}
	}
	tr.mu.Lock()
	defer tr.mu.Unlock()
	return append([]uint64(nil), tr.seen...), append([]uint64(nil), tr.commits...)
}

// Legacy path: etcd publishes the committed index (updateCommittedIndex)
// before the leader tells any follower about the new commit. LeaseRenew and
// LeaseTimeToLive on the leader rely on this (waitAppliedIndex waits for
// applied >= getCommittedIndex()).
func TestReviewLegacyLeaderPublishesCommitBeforeBroadcast(t *testing.T) {
	seen, commits := runLeaderReady(t, false)
	if seen[0] < commits[0] {
		t.Fatalf("legacy: MsgApp with commit %d sent while etcd's committed index was %d", commits[0], seen[0])
	}
}

// Async path: the MsgApp carrying commit 1 is flushed (sendMessages before
// enqueueing the MsgStorageAppend) before updateCommittedIndex runs for the
// MsgStorageApply.
func TestReviewAsyncLeaderBroadcastsCommitBeforePublishingIt(t *testing.T) {
	seen, commits := runLeaderReady(t, true)
	if seen[0] < commits[0] {
		t.Fatalf("async: MsgApp with commit %d sent while etcd's committed index was %d", commits[0], seen[0])
	}
}

// Raft itself (v3.7.0, AsyncStorageWrites) commits an entry on a quorum of
// followers before the leader's own append is durable; the Ready then carries
// the new commit to the followers and in the MsgStorageAppend's HardState, but
// no MsgStorageApply (CommittedEntries are only stable entries). etcd's
// processAsyncReady only calls updateCommittedIndex for MsgStorageApply (and
// snapshots), so etcd's committed index on the leader stays behind what the
// followers apply, however processAsyncReady orders its sends.
func TestReviewRaftAsyncLeaderCommitWithoutApply(t *testing.T) {
	peers := []uint64{1, 2, 3}
	nodes := map[uint64]*raft.RawNode{}
	stores := map[uint64]*raft.MemoryStorage{}
	for _, id := range peers {
		s := raft.NewMemoryStorage()
		snap := raftpb.EnsureSnapshot(nil)
		snap.Metadata.Index = new(uint64(1))
		snap.Metadata.Term = new(uint64(1))
		snap.Metadata.ConfState = &raftpb.ConfState{Voters: peers}
		if err := s.ApplySnapshot(snap); err != nil {
			t.Fatal(err)
		}
		rn, err := raft.NewRawNode(&raft.Config{
			ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: s,
			MaxSizePerMsg: math.MaxUint64, MaxInflightMsgs: 256, AsyncStorageWrites: true,
		})
		if err != nil {
			t.Fatal(err)
		}
		nodes[id], stores[id] = rn, s
	}
	var queue []*raftpb.Message
	var held []*raftpb.Message // leader's MsgStorageAppends we hold back
	holdLeaderAppend := false
	doAppend := func(id uint64, m *raftpb.Message) {
		s := stores[id]
		if snap := m.GetSnapshot(); !raft.IsEmptySnap(snap) {
			s.ApplySnapshot(snap)
		}
		if m.Term != nil {
			s.SetHardState(&raftpb.HardState{Term: m.Term, Vote: m.Vote, Commit: m.Commit})
		}
		s.Append(m.GetEntries())
		queue = append(queue, m.GetResponses()...)
	}
	handle := func(id uint64, rd raft.Ready) {
		for _, m := range rd.Messages {
			switch m.GetTo() {
			case raft.LocalAppendThread:
				if id == 1 && holdLeaderAppend {
					held = append(held, m)
					continue
				}
				doAppend(id, m)
			case raft.LocalApplyThread:
				queue = append(queue, m.GetResponses()...)
			default:
				queue = append(queue, m)
			}
		}
	}
	pump := func() {
		for i := 0; i < 1000; i++ {
			progressed := false
			for _, id := range peers {
				if nodes[id].HasReady() {
					handle(id, nodes[id].Ready())
					progressed = true
				}
			}
			for len(queue) > 0 {
				m := queue[0]
				queue = queue[1:]
				nodes[m.GetTo()].Step(m)
				progressed = true
			}
			if !progressed {
				return
			}
		}
	}
	if err := nodes[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	pump()
	if st := nodes[1].Status(); st.RaftState != raft.StateLeader {
		t.Fatalf("node 1 not leader: %v", st.RaftState)
	}
	commitBefore := nodes[1].Status().GetCommit()

	holdLeaderAppend = true
	if err := nodes[1].Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	rd := nodes[1].Ready()
	handle(1, rd) // MsgApp to 2 and 3 queued; leader's append held
	// deliver to followers, let them persist and answer, deliver answers to 1
	for len(queue) > 0 {
		m := queue[0]
		queue = queue[1:]
		nodes[m.GetTo()].Step(m)
		for _, id := range []uint64{2, 3} {
			for nodes[id].HasReady() {
				handle(id, nodes[id].Ready())
			}
		}
	}
	rd2 := nodes[1].Ready()
	var sawStorageApply bool
	var hsCommit uint64
	var peerCommit uint64
	for _, m := range rd2.Messages {
		switch m.GetTo() {
		case raft.LocalApplyThread:
			sawStorageApply = true
		case raft.LocalAppendThread:
			hsCommit = m.GetCommit()
		default:
			if m.GetCommit() > peerCommit {
				peerCommit = m.GetCommit()
			}
		}
	}
	t.Logf("commit before proposal %d; leader Ready after follower acks: raft commit %d, HardState commit in MsgStorageAppend %d, max commit sent to peers %d, MsgStorageApply present %v, held leader appends %d",
		commitBefore, nodes[1].Status().GetCommit(), hsCommit, peerCommit, sawStorageApply, len(held))
	if peerCommit > commitBefore && !sawStorageApply {
		t.Fatalf("raft broadcast commit %d to followers in a Ready with no MsgStorageApply: etcd's processAsyncReady never calls updateCommittedIndex(%d) for it, so the leader's committed index lags what followers apply", peerCommit, peerCommit)
	}
}
