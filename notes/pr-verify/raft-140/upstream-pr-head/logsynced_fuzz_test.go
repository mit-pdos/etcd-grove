package raft

import (
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestLogSyncedFuzz: a randomized cluster of RawNodes over a lossy, reordering,
// duplicating network, with crashes that lose unpersisted state (persistence only
// in Ready handling, per the RawNode contract), compaction and snapshots,
// ReportUnreachable / ReportSnapshot, MaxSizePerMsg of one entry.
//
// Checks, after every action:
//   - logSynced claim: a follower with logSynced at the term of a live leader has
//     a log that is a prefix of the leader's;
//   - state machine safety: committed entries agree across nodes.
type fzNode struct {
	st *MemoryStorage
	rn *RawNode
}

type fzCluster struct {
	t     *testing.T
	rng   *rand.Rand
	n     int
	nodes map[uint64]*fzNode
	net   []pb.Message
	cfgs  map[uint64]bool
	opts  fzOpts
	trace []string
}

type fzOpts struct {
	preVote, checkQuorum bool
}

func (c *fzCluster) newRN(id uint64, st *MemoryStorage) *RawNode {
	cfg := &Config{
		ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
		MaxSizePerMsg: 1, MaxInflightMsgs: 4,
		PreVote: c.opts.preVote, CheckQuorum: c.opts.checkQuorum,
		Logger: discardLogger,
	}
	rn, err := NewRawNode(cfg)
	if err != nil {
		c.t.Fatal(err)
	}
	return rn
}

func (c *fzCluster) logf(f string, a ...interface{}) {
	c.trace = append(c.trace, fmt.Sprintf(f, a...))
	if len(c.trace) > 400 {
		c.trace = c.trace[len(c.trace)-400:]
	}
}

func (c *fzCluster) ready(id uint64) {
	nd := c.nodes[id]
	if !nd.rn.HasReady() {
		return
	}
	rd := nd.rn.Ready()
	if !IsEmptySnap(rd.Snapshot) {
		if err := nd.st.ApplySnapshot(rd.Snapshot); err != nil {
			c.t.Fatal(err)
		}
	}
	if err := nd.st.Append(rd.Entries); err != nil {
		c.t.Fatal(err)
	}
	if !IsEmptyHardState(rd.HardState) {
		nd.st.SetHardState(rd.HardState)
	}
	for _, m := range rd.Messages {
		c.net = append(c.net, m)
		if m.Type == pb.MsgSnap {
			st := SnapshotFinish
			if c.rng.Intn(3) == 0 {
				st = SnapshotFailure
			}
			nd.rn.ReportSnapshot(m.To, st)
		}
	}
	nd.rn.Advance(rd)
}

func (c *fzCluster) check() {
	// logSynced claim.
	for _, l := range c.nodes {
		lr := l.rn.raft
		if lr.state != StateLeader {
			continue
		}
		for fid, f := range c.nodes {
			fr := f.rn.raft
			if fr.id == lr.id || fr.Term != lr.Term || fr.state != StateFollower || !fr.logSynced {
				continue
			}
			fzStats.syncedChecks++
			if fr.raftLog.lastIndex() > lr.raftLog.lastIndex() {
				c.fail("follower %d (logSynced, term %d) lastIndex %d > leader %d lastIndex %d",
					fid, fr.Term, fr.raftLog.lastIndex(), lr.id, lr.raftLog.lastIndex())
			}
			for i := fr.raftLog.firstIndex(); i <= fr.raftLog.lastIndex(); i++ {
				ft, err1 := fr.raftLog.term(i)
				lt, err2 := lr.raftLog.term(i)
				if err1 == nil && err2 == nil && ft != lt {
					c.fail("follower %d (logSynced, term %d) entry %d term %d, leader %d term %d",
						fid, fr.Term, i, ft, lr.id, lt)
				}
			}
		}
	}
	// Committed entries agree.
	for aid, a := range c.nodes {
		for bid, b := range c.nodes {
			if aid >= bid {
				continue
			}
			ar, br := a.rn.raft, b.rn.raft
			m := min(ar.raftLog.committed, br.raftLog.committed)
			for i := max(ar.raftLog.firstIndex(), br.raftLog.firstIndex()); i <= m; i++ {
				at, e1 := ar.raftLog.term(i)
				bt, e2 := br.raftLog.term(i)
				if e1 == nil && e2 == nil && at != bt {
					c.fail("committed entry %d differs: node %d term %d, node %d term %d", i, aid, at, bid, bt)
				}
			}
		}
	}
}

func (c *fzCluster) fail(f string, a ...interface{}) {
	for _, s := range c.trace {
		c.t.Log(s)
	}
	c.t.Fatalf(f, a...)
}

func (c *fzCluster) step() {
	ids := make([]uint64, 0, c.n)
	for i := 1; i <= c.n; i++ {
		ids = append(ids, uint64(i))
	}
	id := ids[c.rng.Intn(len(ids))]
	nd := c.nodes[id]
	switch r := c.rng.Intn(100); {
	case r < 50 && len(c.net) > 0: // deliver
		k := c.rng.Intn(len(c.net))
		m := c.net[k]
		if c.rng.Intn(10) != 0 { // keep 10% as duplicates
			c.net = append(c.net[:k], c.net[k+1:]...)
		}
		c.logf("deliver %v %d->%d t%d idx%d lt%d ents%d commit%d rej%v", m.Type, m.From, m.To, m.Term, m.Index, m.LogTerm, len(m.Entries), m.Commit, m.Reject)
		tr := c.nodes[m.To].rn.raft
		before := tr.raftLog.lastIndex()
		_ = tr.raftLog
		if m.Type == pb.MsgApp && m.Term == tr.Term {
			end := m.Index + uint64(len(m.Entries))
			if end < before {
				if lt, err := tr.raftLog.term(before); err == nil && lt < m.Term && tr.raftLog.matchTerm(m.Index, m.LogTerm) {
					fzStats.tailAccepts++
				}
			}
		}
		_ = c.nodes[m.To].rn.Step(m)
	case r < 54 && len(c.net) > 0: // drop
		k := c.rng.Intn(len(c.net))
		m := c.net[k]
		c.net = append(c.net[:k], c.net[k+1:]...)
		if c.rng.Intn(2) == 0 {
			c.nodes[m.From].rn.ReportUnreachable(m.To)
		}
	case r < 61:
		nd.rn.Tick()
	case r < 72:
		if nd.rn.raft.state == StateLeader {
			_ = nd.rn.Propose([]byte("x"))
		}
	case r < 90:
		c.ready(id)
	case r < 91: // crash: lose what was not persisted
		c.logf("crash %d", id)
		c.nodes[id] = &fzNode{st: nd.st, rn: c.newRN(id, nd.st)}
	case r < 93: // compact
		applied := nd.rn.raft.raftLog.applied
		cs := pb.ConfState{Voters: ids}
		if _, err := nd.st.CreateSnapshot(applied, &cs, nil); err == nil {
			_ = nd.st.Compact(applied)
		}
	case r < 94:
		c.logf("campaign %d", id)
		_ = nd.rn.Campaign()
	case r < 95:
		_ = nd.rn.ForgetLeader()
	case r < 96:
		if nd.rn.raft.state == StateLeader {
			nd.rn.TransferLeader(ids[c.rng.Intn(len(ids))])
		}
	default:
		c.ready(id)
	}
	c.check()
}

var fzStats struct{ terms, commits, syncedChecks, tailAccepts uint64 }

func TestLogSyncedFuzz(t *testing.T) {
	defer func() { t.Logf("stats %+v", fzStats) }()
	seeds := 300
	if s := os.Getenv("FZ_SEEDS"); s != "" {
		seeds, _ = strconv.Atoi(s)
	}
	for seed := 0; seed < seeds; seed++ {
		rng := rand.New(rand.NewSource(int64(seed)))
		c := &fzCluster{t: t, rng: rng, n: 3 + 2*rng.Intn(2), nodes: map[uint64]*fzNode{},
			opts: fzOpts{preVote: rng.Intn(2) == 0, checkQuorum: rng.Intn(2) == 0}}
		var peers []uint64
		for i := 1; i <= c.n; i++ {
			peers = append(peers, uint64(i))
		}
		for _, id := range peers {
			st := newTestMemoryStorage(withPeers(peers...))
			c.nodes[id] = &fzNode{st: st, rn: c.newRN(id, st)}
		}
		c.logf("seed %d n %d", seed, c.n)
		for i := 0; i < 5000; i++ {
			c.step()
		}
		var maxT, maxC uint64
		stale := 0
		for _, nd := range c.nodes {
			maxT = max(maxT, nd.rn.raft.Term)
			maxC = max(maxC, nd.rn.raft.raftLog.committed)
		}
		fzStats.terms += maxT
		fzStats.commits += maxC
		_ = stale
	}
}
