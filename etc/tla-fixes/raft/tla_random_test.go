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
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// rndRecorder logs every TracingEvent as tla/README.md's example logger does.
type rndRecorder struct{ lines [][]byte }

func (r *rndRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

type rndNode struct {
	rn      *RawNode
	st      *MemoryStorage
	applied uint64
	cs      *pb.ConfState
	// confSinceReady: a configuration change was applied after the node's last Ready, so its
	// persisted configuration (the specification persists it at Ready) is older than the one
	// a restart restores from the application's snapshot; the driver does not restart it then.
	confSinceReady bool
}

type rndOpts struct {
	steps        int
	maxSize      uint64
	maxInflight  int
	restarts     bool
	campaigns    bool
	snapshots    bool
	confChanges  bool
	demotions    bool
	dropPercent  int
	reorder      bool
	nodes        int // members at bootstrap (the rest, up to 5, start empty)
	totalNodes   int
	proposeLimit int
}

type rndCluster struct {
	t        *testing.T
	rng      *rand.Rand
	rec      *rndRecorder
	o        rndOpts
	nodes    map[uint64]*rndNode
	inflight []*pb.Message
	props    int
}

func (c *rndCluster) config(id uint64, st *MemoryStorage, applied uint64) *Config {
	return &Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st, Applied: applied,
		MaxSizePerMsg: c.o.maxSize, MaxInflightMsgs: c.o.maxInflight, TraceLogger: c.rec,
		Logger: discardLogger, PreVote: rndEnvFlag("PREVOTE"), CheckQuorum: rndEnvFlag("CHECKQUORUM")}
}

func (c *rndCluster) ready(id uint64) {
	t, n := c.t, c.nodes[id]
	if !n.rn.HasReady() {
		return
	}
	rd := n.rn.Ready()
	n.confSinceReady = false
	if !IsEmptySnap(rd.Snapshot) {
		if err := n.st.ApplySnapshot(rd.Snapshot); err != nil {
			t.Fatal(err)
		}
		n.applied = rd.Snapshot.GetMetadata().GetIndex()
		n.cs = rd.Snapshot.GetMetadata().GetConfState()
	}
	if err := n.st.Append(rd.Entries); err != nil {
		t.Fatal(err)
	}
	if rd.HardState != nil && !IsEmptyHardState(rd.HardState) {
		if err := n.st.SetHardState(rd.HardState); err != nil {
			t.Fatal(err)
		}
	}
	for _, m := range rd.Messages {
		c.inflight = append(c.inflight, proto.Clone(m).(*pb.Message))
	}
	for _, e := range rd.CommittedEntries {
		if e.GetType() == pb.EntryConfChange {
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				t.Fatal(err)
			}
			n.cs = n.rn.ApplyConfChange(cc)
			n.confSinceReady = true
		}
		n.applied = e.GetIndex()
	}
	n.rn.Advance(rd)
}

func (c *rndCluster) leader() *rndNode {
	for id := uint64(1); id <= uint64(c.o.totalNodes); id++ {
		if n := c.nodes[id]; n.rn.raft.state == StateLeader {
			return n
		}
	}
	return nil
}

func snapHas(m *pb.Message, id uint64) bool {
	cs := m.GetSnapshot().GetMetadata().GetConfState()
	for _, set := range [][]uint64{cs.GetVoters(), cs.GetLearners(), cs.GetVotersOutgoing()} {
		for _, v := range set {
			if v == id {
				return true
			}
		}
	}
	return false
}

func (c *rndCluster) deliver(i int, drop bool) {
	m := c.inflight[i]
	c.inflight = append(c.inflight[:i:i], c.inflight[i+1:]...)
	src := c.nodes[m.GetFrom()]
	if m.GetType() == pb.MessageType_MsgSnap && !snapHas(m, m.GetTo()) {
		// raft ignores a snapshot whose configuration does not include the receiver ("should
		// never happen", raft.restore): an application does not send one; the transport
		// loses it here.
		drop = true
	}
	if drop {
		src.rn.ReportUnreachable(m.GetTo())
		if m.GetType() == pb.MessageType_MsgSnap {
			src.rn.ReportSnapshot(m.GetTo(), SnapshotFailure)
		}
		return
	}
	if err := c.nodes[m.GetTo()].rn.Step(m); err != nil && err != ErrStepPeerNotFound {
		c.t.Fatal(err)
	}
	if m.GetType() == pb.MessageType_MsgSnap {
		src.rn.ReportSnapshot(m.GetTo(), SnapshotFinish)
	}
}

func (c *rndCluster) step() {
	r := c.rng.Intn(100)
	ids := uint64(c.o.totalNodes)
	id := uint64(c.rng.Intn(int(ids))) + 1
	n := c.nodes[id]
	switch {
	case r < 40 && len(c.inflight) > 0:
		i := 0
		if c.o.reorder {
			i = c.rng.Intn(len(c.inflight))
		}
		c.deliver(i, c.rng.Intn(100) < c.o.dropPercent)
	case r < 62:
		c.ready(id)
	case r < 70:
		// time passes for every node
		for j := uint64(1); j <= ids; j++ {
			c.nodes[j].rn.Tick()
		}
	case r < 80:
		if l := c.leader(); l != nil && c.props < c.o.proposeLimit {
			c.props++
			_ = l.rn.Propose([]byte(fmt.Sprintf("v%d", c.props)))
		}
	case r < 85 && c.o.confChanges:
		l := c.leader()
		if l == nil {
			return
		}
		j := uint64(c.rng.Intn(int(ids))) + 1
		voters := map[uint64]bool{}
		for v := range l.rn.raft.trk.Voters[0] {
			voters[v] = true
		}
		learners := map[uint64]bool{}
		for v := range l.rn.raft.trk.Learners {
			learners[v] = true
		}
		var typ pb.ConfChangeType
		switch c.rng.Intn(3) {
		case 0:
			if voters[j] {
				return // a no-op in raft, which the specification's AddNewServer excludes
			}
			typ = pb.ConfChangeAddNode
		case 1:
			if !voters[j] && !learners[j] {
				return
			}
			if voters[j] && len(voters) <= 2 {
				return // keep a majority alive enough to make progress
			}
			if j == l.rn.raft.id {
				return
			}
			typ = pb.ConfChangeRemoveNode
		default:
			if learners[j] {
				return // a no-op in raft, which the specification's AddLearner excludes
			}
			if voters[j] && (!c.o.demotions || len(voters) <= 2 || j == l.rn.raft.id) {
				return
			}
			typ = pb.ConfChangeAddLearnerNode
		}
		_ = l.rn.ProposeConfChange(&pb.ConfChange{Type: typ.Enum(), NodeId: proto.Uint64(j)})
	case r < 90 && c.o.snapshots:
		if n.applied > 0 && n.cs != nil {
			if _, err := n.st.CreateSnapshot(n.applied, n.cs, nil); err == nil {
				_ = n.st.Compact(n.applied)
			}
		}
	case r < 92 && c.o.campaigns:
		// a node's election timeout fires early (a partitioned or slow node, an operator's
		// Campaign): competing candidates, and leaders replaced with entries uncommitted
		_ = n.rn.Campaign()
	case r < 94 && c.o.restarts:
		nosnap := os.Getenv("TLA_RESTART_NOSNAP") != ""
		if (n.confSinceReady && !nosnap) || n.cs == nil {
			return
		}
		// The application persists its applied configuration with a snapshot at what it
		// applied, as a restarted raft restores the configuration from the storage's snapshot.
		applied := n.applied
		if !nosnap {
			if _, err := n.st.CreateSnapshot(n.applied, n.cs, nil); err != nil && err != ErrSnapOutOfDate {
				c.t.Fatal(err)
			}
		} else {
			// The application persisted nothing of its own: it re-applies from its storage's
			// snapshot (the configuration raft restores).
			snap, _ := n.st.Snapshot()
			applied = snap.GetMetadata().GetIndex()
			n.applied = applied
			n.cs = snap.GetMetadata().GetConfState()
		}
		rn, err := NewRawNode(c.config(id, n.st, applied))
		if err != nil {
			c.t.Fatal(err)
		}
		n.rn = rn
	}
}


func runRandom(t *testing.T, seed int64, o rndOpts) (*rndRecorder, error) {
	rec := &rndRecorder{}
	c := &rndCluster{t: t, rng: rand.New(rand.NewSource(seed)), rec: rec, o: o, nodes: map[uint64]*rndNode{}}
	var peers []Peer
	for id := uint64(1); id <= uint64(o.nodes); id++ {
		peers = append(peers, Peer{ID: id})
	}
	for id := uint64(1); id <= uint64(o.totalNodes); id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(c.config(id, st, 0))
		if err != nil {
			t.Fatal(err)
		}
		if id <= uint64(o.nodes) {
			if err := rn.Bootstrap(peers); err != nil {
				t.Fatal(err)
			}
		}
		c.nodes[id] = &rndNode{rn: rn, st: st}
	}
	for id := uint64(1); id <= uint64(o.nodes); id++ {
		c.ready(id)
	}
	var perr error
	func() {
		defer func() {
			if r := recover(); r != nil {
				perr = fmt.Errorf("raft panicked: %v", r)
			}
		}()
		for s := 0; s < o.steps; s++ {
			c.step()
		}
	}()
	return rec, perr
}

var rndLineRe = regexp.MustCompile(`l = (\d+)`)

// validateTrace runs Traceetcdraft on the lines as tla/validate.sh does; it returns "" if the
// trace is accepted, else TLC's error lines.
func validateTrace(t *testing.T, tools, spec string, lines [][]byte) string {
	dir := t.TempDir()
	trace := filepath.Join(dir, "trace.ndjson")
	f, err := os.Create(trace)
	if err != nil {
		t.Fatal(err)
	}
	for _, l := range lines {
		fmt.Fprintf(f, "%s\n", l)
	}
	f.Close()
	cmd := exec.Command("java", "-XX:+UseParallelGC",
		"-cp", filepath.Join(tools, "tla2tools.jar")+":"+filepath.Join(tools, "CommunityModules-deps.jar"),
		"tlc2.TLC", "-config", "Traceetcdraft.cfg", "Traceetcdraft.tla", "-lncheck", "final",
		"-metadir", filepath.Join(dir, "state"))
	cmd.Dir = spec
	cmd.Env = append(os.Environ(), "JSON="+trace)
	out, err := cmd.CombinedOutput()
	if err == nil {
		return ""
	}
	var errs []string
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, "Error: ") && !strings.Contains(l, "behavior") && !strings.Contains(l, "counter-example") {
			errs = append(errs, l)
		}
	}
	last := 0
	for _, m := range rndLineRe.FindAllStringSubmatch(string(out), -1) {
		if v, _ := strconv.Atoi(m[1]); v > last {
			last = v
		}
	}
	msg := strings.Join(errs, "; ")
	if last >= 1 && last <= len(lines) {
		msg += fmt.Sprintf(" [unmatched line %d of %d: %s]", last, len(lines), lines[last-1])
	}
	if msg == "" {
		msg = fmt.Sprintf("TLC failed: %v\n%s", err, out)
	}
	return msg
}

func rndEnvInt(name string, def int) int {
	if v, err := strconv.Atoi(os.Getenv(name)); err == nil {
		return v
	}
	return def
}

// TestTLARandom runs random clusters of RawNodes and validates each trace with
// tla/Traceetcdraft.tla. TLA_SEEDS (default 20) seeds from TLA_SEED0 (default 1); TLA_STEPS
// steps each (default 300); TLA_FEATURES a comma-separated subset of
// restarts,snapshots,conf,demote,drop,reorder,cut,throttle,campaign (default all).
func TestTLARandom(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	spec, err := filepath.Abs("tla")
	if err != nil {
		t.Fatal(err)
	}
	feats := map[string]bool{}
	fs := os.Getenv("TLA_FEATURES")
	if fs == "" {
		fs = "restarts,snapshots,conf,demote,drop,reorder,cut,throttle,campaign"
	}
	for _, f := range strings.Split(fs, ",") {
		feats[f] = true
	}
	seeds := rndEnvInt("TLA_SEEDS", 20)
	seed0 := rndEnvInt("TLA_SEED0", 1)
	steps := rndEnvInt("TLA_STEPS", 300)
	failed := 0
	for s := seed0; s < seed0+seeds; s++ {
		o := rndOpts{steps: steps, maxSize: 4096, maxInflight: 256, nodes: 3, totalNodes: 5,
			proposeLimit: 1000, restarts: feats["restarts"], snapshots: feats["snapshots"],
			confChanges: feats["conf"], demotions: feats["demote"], reorder: feats["reorder"],
			campaigns: feats["campaign"]}
		if feats["drop"] {
			o.dropPercent = 10
		}
		if feats["cut"] && s%2 == 0 {
			o.maxSize = 1
		}
		if feats["throttle"] && s%3 == 0 {
			o.maxInflight = 2
		}
		if !feats["conf"] {
			o.totalNodes = 3
		}
		rec, perr := runRandom(t, int64(s), o)
		if perr != nil {
			t.Errorf("seed %d: %v", s, perr)
			failed++
			continue
		}
		if msg := validateTrace(t, tools, spec, rec.lines); msg != "" {
			t.Errorf("seed %d (%d lines): rejected: %s", s, len(rec.lines), msg)
			failed++
			if d := os.Getenv("TLA_KEEP"); d != "" {
				f, _ := os.Create(filepath.Join(d, fmt.Sprintf("seed%d.ndjson", s)))
				for _, l := range rec.lines {
					fmt.Fprintf(f, "%s\n", l)
				}
				f.Close()
			}
		} else {
			t.Logf("seed %d (%d lines): accepted", s, len(rec.lines))
			if d := os.Getenv("TLA_KEEPALL"); d != "" {
				f, _ := os.Create(filepath.Join(d, fmt.Sprintf("seed%d.ndjson", s)))
				for _, l := range rec.lines {
					fmt.Fprintf(f, "%s\n", l)
				}
				f.Close()
			}
		}
	}
	t.Logf("%d of %d seeds failed", failed, seeds)
}

// rndEnvFlag reads raft's PreVote or CheckQuorum from the environment variable TLC's
// Traceetcdraft reads too ("1" or "true").
func rndEnvFlag(name string) bool {
	v := os.Getenv(name)
	return v == "1" || v == "true"
}
