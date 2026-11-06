// Package winpendprobe is a deterministic in-process simulation of a 3-member
// raft v3.7.0 cluster driven the way etcd's raft loop (server/etcdserver/raft.go
// at etcd 673da07c8) drives raft.Node, to measure how often the restart premise
// "Hwpend" fails: a replay batch's raftTerm equals the term of a MsgSnap this
// member has sent.
//
// What it models, per member:
//   - raft.RawNode over a MemoryStorage that stands for the persisted WAL + snap
//     (everything a Ready hands out is persisted before Advance, as etcd does);
//   - etcd's raftTerm: 0 at each incarnation's start, set to rd.HardState.Term
//     at every non-empty HardState (raft.go:183,222-224), stamped on each
//     toApply batch (raft.go:234);
//   - an apply loop lagging behind the raft loop (batches queued, applied a few
//     per round), with etcd's snapshot+compaction (CreateSnapshot at the applied
//     index every SnapCount applied entries, Compact keeping CatchUp entries);
//   - MsgSnap emitted by raft (recorded with its term, as processMessages puts it
//     in msgSnapC), delivered to the follower, ReportSnapshot on delivery/drop;
//   - kill = drop all volatile state (queued batches, inflight msgs to/from it);
//     restart = RawNode over a copy of the storage, Config.Applied = 0 (etcd's
//     raftConfig does not set it), so raft re-hands out (snapshot, commit].
//
// What it does not model: wall-clock timing (one round = one tick = one
// message hop), the server-side merge itself, conf changes, the v2 store,
// backend consistent-index skipping (batches still flow, so it does not matter
// for raftTerm), the fact that etcd's real SnapshotCount/catch-up are 10000/5000.
package winpendprobe

import (
	"fmt"
	"math/rand"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

type Params struct {
	Seed              int64
	SnapCount         uint64 // apply entries between snapshots
	CatchUp           uint64 // entries kept after compaction
	ApplyPerRound     int    // batches applied per round
	ReadyPerRound     int    // Readys the raft loop handles per round (0 = drain)
	MaxCommittedReady uint64 // raft MaxCommittedSizePerReady (0 = MaxSizePerMsg)
	PreVote           bool
}

type batch struct {
	ents    []*pb.Entry
	snapIdx uint64
	rt      uint64
	replay  bool
	inc     int
}

type member struct {
	id       uint64
	rn       *raft.RawNode
	st       *raft.MemoryStorage
	alive    bool
	inc      int    // incarnation number
	raftTerm uint64 // etcd's raftTerm (per incarnation)
	queue    []batch
	applied  uint64
	snapIdx  uint64
	// restart bookkeeping
	replayCommit uint64 // HardState.Commit at the latest restart (0 = first start)
	everLeader   map[uint64]bool
	restoredTerm uint64 // HardState.Term at the latest restart
	restoredLast uint64 // restored log's last index at the latest restart
	handedOut    uint64 // highest committed index handed out in this incarnation
}

type msgSnapRec struct {
	term  uint64
	round int
	inc   int
}

type ReplayBatch struct {
	Member  uint64
	Inc     int
	Rt      uint64
	Round   int  // round at which it was applied (or -1: killed before apply)
	FailNow bool // a MsgSnap at term Rt was sent by this member before the batch was applied
	FailAny bool // ... at any time in the run
}

type Restart struct {
	Member       uint64
	Round        int
	HSTerm       uint64
	WasLeaderAtT bool // it was leader at its HardState term when killed
	SentSnapAtT  bool // it sent a MsgSnap at HSTerm (the term T the brief asks about)
	ReplayLen    uint64
	Batches      []*ReplayBatch
	AppliedAny   bool // A0 nonempty proxy: something was applied in the earlier incarnation(s)
}

type Sim struct {
	P        Params
	rng      *rand.Rand
	m        map[uint64]*member
	inflight []*pb.Message
	next     []*pb.Message
	Round    int
	parted   map[uint64]bool
	SentSnap map[uint64][]msgSnapRec
	// commitTerms: terms t at which some leader advanced its commit (commitWit t c)
	CommitTerms map[uint64]bool
	Restarts    []*Restart
	cur         map[uint64]*Restart
	Log         []string
	Verbose     bool
}

var ids = []uint64{1, 2, 3}

func cs() *pb.ConfState { return &pb.ConfState{Voters: []uint64{1, 2, 3}} }

func NewSim(p Params) *Sim {
	s := &Sim{P: p, rng: rand.New(rand.NewSource(p.Seed)), m: map[uint64]*member{},
		parted: map[uint64]bool{}, SentSnap: map[uint64][]msgSnapRec{},
		CommitTerms: map[uint64]bool{}, cur: map[uint64]*Restart{}}
	for _, id := range ids {
		st := raft.NewMemoryStorage()
		st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: proto.Uint64(1), Term: proto.Uint64(1), ConfState: cs()}})
		mb := &member{id: id, st: st, applied: 1, snapIdx: 1, everLeader: map[uint64]bool{}}
		s.m[id] = mb
		s.boot(mb)
	}
	return s
}

func (s *Sim) logf(f string, a ...any) {
	if s.Verbose {
		s.Log = append(s.Log, fmt.Sprintf("[r%d] ", s.Round)+fmt.Sprintf(f, a...))
	}
}

func (s *Sim) boot(mb *member) {
	cfg := &raft.Config{ID: mb.id, ElectionTick: 10, HeartbeatTick: 1, Storage: mb.st,
		MaxSizePerMsg: 1024 * 1024, MaxInflightMsgs: 256, CheckQuorum: true, PreVote: s.P.PreVote,
		MaxCommittedSizePerReady: s.P.MaxCommittedReady,
		Logger:                   &raft.DefaultLogger{Logger: discard}}
	rn, err := raft.NewRawNode(cfg)
	if err != nil {
		panic(err)
	}
	mb.rn = rn
	mb.alive = true
	mb.raftTerm = 0
	mb.queue = nil
}

func (s *Sim) Leader() uint64 {
	for _, id := range ids {
		mb := s.m[id]
		if mb.alive && mb.rn.BasicStatus().RaftState == raft.StateLeader {
			return id
		}
	}
	return 0
}

func (s *Sim) Term(id uint64) uint64 { return s.m[id].rn.BasicStatus().GetTerm() }

func (s *Sim) Partition(id uint64, on bool) { s.parted[id] = on }

func (s *Sim) Campaign(id uint64) { s.m[id].rn.Campaign() }

func (s *Sim) Propose(n int) {
	l := s.Leader()
	if l == 0 {
		return
	}
	for i := 0; i < n; i++ {
		s.m[l].rn.Propose([]byte(fmt.Sprintf("v%06d", s.rng.Intn(1000000))))
	}
}

func (s *Sim) Kill(id uint64) {
	mb := s.m[id]
	if !mb.alive {
		return
	}
	bs := mb.rn.BasicStatus()
	s.logf("kill %d (state %v term %d commit %d applied %d)", id, bs.RaftState, bs.GetTerm(), bs.GetCommit(), mb.applied)
	// close out the previous incarnation's replay record
	delete(s.cur, id)
	// remember whether it was leader at its current term
	if bs.RaftState == raft.StateLeader {
		mb.everLeader[bs.GetTerm()] = true
	}
	mb.alive = false
	mb.queue = nil
	// persisted state = the storage; copy it (the WAL + snap files)
	old := mb.st
	snap, _ := old.Snapshot()
	hs, _, _ := old.InitialState()
	fi, _ := old.FirstIndex()
	li, _ := old.LastIndex()
	ents, _ := old.Entries(fi, li+1, ^uint64(0))
	st := raft.NewMemoryStorage()
	st.ApplySnapshot(proto.Clone(snap).(*pb.Snapshot))
	cl := make([]*pb.Entry, len(ents))
	for i, e := range ents {
		cl[i] = proto.Clone(e).(*pb.Entry)
	}
	st.Append(cl)
	st.SetHardState(proto.Clone(hs).(*pb.HardState))
	mb.st = st
}

func (s *Sim) RestartMember(id uint64) {
	mb := s.m[id]
	if mb.alive {
		return
	}
	hs, _, _ := mb.st.InitialState()
	snap, _ := mb.st.Snapshot()
	mb.inc++
	r := &Restart{Member: id, Round: s.Round, HSTerm: hs.GetTerm(), WasLeaderAtT: mb.everLeader[hs.GetTerm()],
		ReplayLen: hs.GetCommit() - snap.GetMetadata().GetIndex(), AppliedAny: mb.applied > 1}
	for _, rec := range s.SentSnap[id] {
		if rec.term == hs.GetTerm() {
			r.SentSnapAtT = true
		}
	}
	mb.replayCommit = hs.GetCommit()
	mb.restoredTerm = hs.GetTerm()
	mb.restoredLast, _ = mb.st.LastIndex()
	mb.applied = snap.GetMetadata().GetIndex()
	mb.handedOut = mb.applied // the restored snapshot index: the window is (snap, commit]
	mb.snapIdx = mb.applied
	s.Restarts = append(s.Restarts, r)
	s.cur[id] = r
	s.logf("restart %d: HS term %d commit %d snap %d", id, hs.GetTerm(), hs.GetCommit(), mb.applied)
	s.boot(mb)
}

func (s *Sim) cut(a, b uint64) bool {
	return !s.m[a].alive || !s.m[b].alive || s.parted[a] || s.parted[b]
}

// Step runs one round: deliver messages, tick, raft loop, apply loop.
func (s *Sim) Step() {
	s.Round++
	msgs := s.inflight
	s.inflight = nil
	for _, m := range msgs {
		from, to := m.GetFrom(), m.GetTo()
		if s.cut(from, to) {
			if m.GetType() == pb.MsgSnap && s.m[from].alive {
				s.m[from].rn.ReportSnapshot(to, raft.SnapshotFailure)
			}
			continue
		}
		s.m[to].rn.Step(m)
		if m.GetType() == pb.MsgSnap && s.m[from].alive {
			s.m[from].rn.ReportSnapshot(to, raft.SnapshotFinish)
		}
	}
	for _, id := range ids {
		mb := s.m[id]
		if !mb.alive {
			continue
		}
		mb.rn.Tick()
		s.raftLoop(mb)
	}
	for _, id := range ids {
		mb := s.m[id]
		if mb.alive {
			s.applyLoop(mb)
		}
	}
}

func (s *Sim) raftLoop(mb *member) {
	n := 0
	for mb.rn.HasReady() {
		if s.P.ReadyPerRound > 0 && n >= s.P.ReadyPerRound {
			break
		}
		n++
		rd := mb.rn.Ready()
		bs := mb.rn.BasicStatus()
		if bs.RaftState == raft.StateLeader {
			mb.everLeader[bs.GetTerm()] = true
		}
		if !raft.IsEmptyHardState(rd.HardState) {
			prev, _, _ := mb.st.InitialState()
			if bs.RaftState == raft.StateLeader && rd.HardState.GetCommit() > prev.GetCommit() {
				s.CommitTerms[rd.HardState.GetTerm()] = true
			}
			mb.raftTerm = rd.HardState.GetTerm()
		}
		b := batch{ents: rd.CommittedEntries, rt: mb.raftTerm, inc: mb.inc}
		for _, e := range rd.CommittedEntries {
			if e.GetIndex() > mb.handedOut {
				mb.handedOut = e.GetIndex()
			}
		}
		if !raft.IsEmptySnap(rd.Snapshot) && mb.inc > 0 {
			si := rd.Snapshot.GetMetadata().GetIndex()
			pendApply := mb.applied < mb.replayCommit
			for _, q := range mb.queue { // queued, not yet applied
				for _, e := range q.ents {
					if e.GetIndex() <= mb.replayCommit {
						pendApply = true
					}
				}
			}
			pendRaft := mb.handedOut < mb.replayCommit
			if pendApply || pendRaft {
				Totals.InstallsInWindow++
				ghost := mb.restoredLast
				switch {
				case si < ghost:
					Totals.SnapLtGhost++
				case si == ghost:
					Totals.SnapEqGhost++
				default:
					Totals.SnapGtGhost++
				}
				if si <= mb.replayCommit {
					Totals.SnapLeReplayCommit++
				}
				kind := "<"
				if si == ghost {
					kind = "="
				}
				if si <= ghost && Totals.traced[kind] < 2 {
					if Totals.traced == nil {
						Totals.traced = map[string]int{}
					}
					Totals.traced[kind]++
					tt, _ := mb.st.Term(si)
					Totals.Traces = append(Totals.Traces, fmt.Sprintf("["+kind+"] restored-log term at snap idx %d, leader %d; ", tt, rd.Snapshot.GetMetadata().GetTerm())+fmt.Sprintf("seed %d r%d m%d inc %d: snap idx %d term %d; restored last %d (term of restored HS %d), commit at restart %d, applied %d, handed out %d, pendApply %v pendRaft %v",
						s.P.Seed, s.Round, mb.id, mb.inc, si, rd.Snapshot.GetMetadata().GetTerm(), mb.restoredLast, mb.restoredTerm, mb.replayCommit, mb.applied, mb.handedOut, pendApply, pendRaft))
				}
			} else {
				Totals.InstallsOutsideWindow++
			}
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			b.snapIdx = rd.Snapshot.GetMetadata().GetIndex()
		}
		if mb.inc > 0 {
			for _, e := range rd.CommittedEntries {
				if e.GetIndex() <= mb.replayCommit {
					b.replay = true
				}
			}
		}
		if len(b.ents) > 0 || b.snapIdx > 0 {
			mb.queue = append(mb.queue, b)
		}
		// messages: MsgSnap goes to msgSnapC in etcd; record it with its term
		for _, m := range rd.Messages {
			if m.GetType() == pb.MsgSnap {
				if mb.inc > 0 {
					Totals.RestartedMsgSnaps++
					if m.GetTerm() <= mb.restoredTerm {
						Totals.RestartedMsgSnapBad++
						if len(Totals.Traces) < 6 {
							Totals.Traces = append(Totals.Traces, fmt.Sprintf("BAD MsgSnap seed %d r%d m%d term %d restoredTerm %d", s.P.Seed, s.Round, mb.id, m.GetTerm(), mb.restoredTerm))
						}
					}
				}
				s.SentSnap[mb.id] = append(s.SentSnap[mb.id], msgSnapRec{term: m.GetTerm(), round: s.Round, inc: mb.inc})
				s.logf("%d sends MsgSnap term %d to %d (snap idx %d)", mb.id, m.GetTerm(), m.GetTo(), m.GetSnapshot().GetMetadata().GetIndex())
			}
			s.inflight = append(s.inflight, proto.Clone(m).(*pb.Message))
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			mb.st.ApplySnapshot(proto.Clone(rd.Snapshot).(*pb.Snapshot))
		}
		if !raft.IsEmptyHardState(rd.HardState) {
			mb.st.SetHardState(proto.Clone(rd.HardState).(*pb.HardState))
		}
		if len(rd.Entries) > 0 {
			cl := make([]*pb.Entry, len(rd.Entries))
			for i, e := range rd.Entries {
				cl[i] = proto.Clone(e).(*pb.Entry)
			}
			mb.st.Append(cl)
		}
		mb.rn.Advance(rd)
	}
}

func (s *Sim) applyLoop(mb *member) {
	for k := 0; k < s.P.ApplyPerRound && len(mb.queue) > 0; k++ {
		b := mb.queue[0]
		mb.queue = mb.queue[1:]
		if b.snapIdx > mb.applied {
			mb.applied = b.snapIdx
			mb.snapIdx = b.snapIdx
		}
		for _, e := range b.ents {
			if e.GetIndex() > mb.applied {
				mb.applied = e.GetIndex()
			}
		}
		if b.replay {
			r := s.cur[mb.id]
			rb := &ReplayBatch{Member: mb.id, Inc: b.inc, Rt: b.rt, Round: s.Round}
			for _, rec := range s.SentSnap[mb.id] {
				if rec.term == b.rt {
					rb.FailNow = true
				}
			}
			if r != nil {
				r.Batches = append(r.Batches, rb)
			}
		}
		// etcd: snapshotIfNeededAndCompactRaftLog
		if mb.applied-mb.snapIdx > s.P.SnapCount {
			if _, err := mb.st.CreateSnapshot(mb.applied, cs(), nil); err == nil {
				mb.snapIdx = mb.applied
				if mb.applied > s.P.CatchUp {
					mb.st.Compact(mb.applied - s.P.CatchUp)
				}
			}
		}
	}
}

// Finish computes FailAny over the whole run.
func (s *Sim) Finish() {
	for _, r := range s.Restarts {
		for _, b := range r.Batches {
			for _, rec := range s.SentSnap[b.Member] {
				if rec.term == b.Rt {
					b.FailAny = true
				}
			}
		}
	}
}

// LeanTextFails: the Lean premise as written quantifies over every rt with
// rnRtOk (rt = 0 or a term with a commit witness c >= n, n < |a0|), not only
// the raftTerms that occur. Proxy: a0 nonempty and the member sent a MsgSnap at
// some term at which a leader committed.
func (s *Sim) LeanTextFails(r *Restart) bool {
	if !r.AppliedAny {
		return false
	}
	for _, rec := range s.SentSnap[r.Member] {
		if s.CommitTerms[rec.term] {
			return true
		}
	}
	return false
}

// Totals accumulates the follow-up checks over every Sim of a test binary run.
var Totals struct {
	RestartedMsgSnaps, RestartedMsgSnapBad                    int
	InstallsInWindow, InstallsOutsideWindow                   int
	SnapLtGhost, SnapEqGhost, SnapGtGhost, SnapLeReplayCommit int
	Traces                                                    []string
	traced                                                    map[string]int
}
