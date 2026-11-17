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
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// snapCFRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON line
// per event, the event in the "event" field), in the order raft emits them.
type snapCFRecorder struct{ lines [][]byte }

func (r *snapCFRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// snapCFNode is one member: its RawNode, its storage, and what its application has applied.
type snapCFNode struct {
	rn      *RawNode
	st      *MemoryStorage
	applied uint64
	cs      *pb.ConfState
}

// snapCFCluster is three RawNodes and the messages in flight between them, delivered by the
// test.
type snapCFCluster struct {
	t        *testing.T
	nodes    map[uint64]*snapCFNode
	inflight []*pb.Message
}

// ready handles id's Ready as an application does: installs the snapshot, persists the entries
// and hard state, sends the messages, applies the committed entries (configuration changes
// through ApplyConfChange), and advances.
func (c *snapCFCluster) ready(id uint64) {
	t, n := c.t, c.nodes[id]
	if !n.rn.HasReady() {
		return
	}
	rd := n.rn.Ready()
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
		}
		n.applied = e.GetIndex()
	}
	n.rn.Advance(rd)
}

// flush handles every node's Ready and delivers the messages in flight in the order they were
// sent, until none is left; a message for which drop holds is lost (and reported unreachable,
// as etcd's transport does).
func (c *snapCFCluster) flush(drop func(m *pb.Message) bool) {
	for {
		for id := uint64(1); id <= 3; id++ {
			c.ready(id)
		}
		if len(c.inflight) == 0 {
			return
		}
		m := c.inflight[0]
		c.inflight = c.inflight[1:]
		src := c.nodes[m.GetFrom()]
		if drop(m) {
			src.rn.ReportUnreachable(m.GetTo())
			if m.GetType() == pb.MessageType_MsgSnap {
				src.rn.ReportSnapshot(m.GetTo(), SnapshotFailure)
			}
			continue
		}
		if err := c.nodes[m.GetTo()].rn.Step(m); err != nil {
			c.t.Fatal(err)
		}
		if m.GetType() == pb.MessageType_MsgSnap {
			src.rn.ReportSnapshot(m.GetTo(), SnapshotFinish)
		}
	}
}

// TestTLATraceSnapshotToCommittedFollower runs three RawNodes, configured as tla/README.md's
// example, through a schedule where the leader sends a snapshot to a follower that lags behind
// its compacted log, and validates the trace with tla/Traceetcdraft.tla as tla/validate.sh does.
// Every step is ordinary raft behavior (the follower installs the snapshot), yet TLC rejects the
// trace: the specification cannot install a snapshot on a follower that has committed anything,
// and every bootstrapped member has.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceSnapshotToCommittedFollower(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &snapCFRecorder{}
	c := &snapCFCluster{t: t, nodes: map[uint64]*snapCFNode{}}
	for id := uint64(1); id <= 3; id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(&Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
			MaxSizePerMsg: 4096, MaxInflightMsgs: 256, TraceLogger: rec})
		if err != nil {
			t.Fatal(err)
		}
		if err := rn.Bootstrap([]Peer{{ID: 1}, {ID: 2}, {ID: 3}}); err != nil {
			t.Fatal(err)
		}
		c.nodes[id] = &snapCFNode{rn: rn, st: st}
	}
	none := func(*pb.Message) bool { return false }
	to3 := func(m *pb.Message) bool { return m.GetTo() == 3 }
	c.flush(none) // each node applies the bootstrap configuration

	// Term 2: node 1 is elected with every vote; from then on, everything sent to node 3 is lost
	// until the leader has compacted its log. Node 3 has committed the three bootstrap entries.
	if err := c.nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.flush(func(m *pb.Message) bool { return m.GetTo() == 3 && m.GetType() != pb.MessageType_MsgVote })
	if err := c.nodes[1].rn.Propose([]byte("a")); err != nil {
		t.Fatal(err)
	}
	if err := c.nodes[1].rn.Propose([]byte("b")); err != nil {
		t.Fatal(err)
	}
	c.flush(to3)
	leader := c.nodes[1]
	if s := leader.rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetCommit() != 6 || leader.applied != 6 {
		t.Fatalf("node 1: %v commit %d applied %d, want leader with 6 committed and applied",
			s.RaftState, s.HardState.GetCommit(), leader.applied)
	}
	committed3 := c.nodes[3].rn.BasicStatus().HardState.GetCommit()
	if committed3 < 1 || committed3 >= 6 {
		t.Fatalf("node 3: commit %d, want a follower that has committed something, but not index 6", committed3)
	}

	// The leader's application takes a snapshot of what it applied, its configuration including
	// node 3, and compacts its log.
	if _, err := leader.st.CreateSnapshot(leader.applied, leader.cs, nil); err != nil {
		t.Fatal(err)
	}
	if err := leader.st.Compact(leader.applied); err != nil {
		t.Fatal(err)
	}

	// A heartbeat: node 3's response makes the leader send it the snapshot, which node 3
	// installs.
	leader.rn.Tick()
	c.flush(none)

	sawSnap := false
	for _, l := range rec.lines {
		if strings.Contains(string(l), `"type":"MsgSnap","term":2,"from":"1","to":"3"`) {
			sawSnap = true
		}
	}
	if !sawSnap {
		t.Fatalf("no MsgSnap 1->3 in the trace")
	}
	n3 := c.nodes[3]
	if s := n3.rn.BasicStatus(); s.HardState.GetCommit() != 6 || n3.applied != 6 {
		t.Fatalf("node 3: commit %d applied %d, want the snapshot at 6 installed", s.HardState.GetCommit(), n3.applied)
	}
	if snap, err := n3.st.Snapshot(); err != nil || snap.GetMetadata().GetIndex() != 6 {
		t.Fatalf("node 3's storage: snapshot %v (%v), want index 6", snap.GetMetadata(), err)
	}
	if pr := leader.rn.Status().Progress[3]; pr.Match != 6 {
		t.Fatalf("leader's progress of node 3: match %d, want 6", pr.Match)
	}

	dir := t.TempDir()
	trace := filepath.Join(dir, "trace.ndjson")
	f, err := os.Create(trace)
	if err != nil {
		t.Fatal(err)
	}
	for _, l := range rec.lines {
		fmt.Fprintf(f, "%s\n", l)
	}
	f.Close()
	spec, err := filepath.Abs("tla")
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("java", "-XX:+UseParallelGC",
		"-cp", filepath.Join(tools, "tla2tools.jar")+":"+filepath.Join(tools, "CommunityModules-deps.jar"),
		"tlc2.TLC", "-config", "Traceetcdraft.cfg", "Traceetcdraft.tla", "-lncheck", "final",
		"-metadir", filepath.Join(dir, "state"))
	cmd.Dir = spec
	cmd.Env = append(os.Environ(), "JSON="+trace)
	out, err := cmd.CombinedOutput()
	if err != nil {
		for _, l := range snapCFLines(out, "Error: ") {
			t.Log(l)
		}
		if n := snapCFLastLine(out); n >= 1 && n <= len(rec.lines) {
			t.Logf("TLC matched lines 1-%d of %d; line %d: %s", n-1, len(rec.lines), n, rec.lines[n-1])
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func snapCFLines(out []byte, prefix string) []string {
	var ls []string
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, prefix) {
			ls = append(ls, l)
		}
	}
	return ls
}

// snapCFLastLine is the trace line TLC's counterexample stops at (the value of l in its last
// state), or 0.
func snapCFLastLine(out []byte) int {
	n := 0
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, "/\\ l = ") {
			fmt.Sscanf(strings.TrimPrefix(l, "/\\ l = "), "%d", &n)
		}
	}
	return n
}
