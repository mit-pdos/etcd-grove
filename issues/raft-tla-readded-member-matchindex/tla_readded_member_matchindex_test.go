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

// readdMIRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON line
// per event, the event in the "event" field), in the order raft emits them.
type readdMIRecorder struct{ lines [][]byte }

func (r *readdMIRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// readdMINode is one member: its RawNode, its storage, and what its application has applied.
type readdMINode struct {
	rn      *RawNode
	st      *MemoryStorage
	applied uint64
	cs      *pb.ConfState
}

// readdMICluster is three RawNodes and the messages in flight between them, delivered by the
// test.
type readdMICluster struct {
	t        *testing.T
	nodes    map[uint64]*readdMINode
	inflight []*pb.Message
}

// ready handles id's Ready as an application does: installs the snapshot, persists the entries
// and hard state, sends the messages, applies the committed entries (configuration changes
// through ApplyConfChange), and advances.
func (c *readdMICluster) ready(id uint64) {
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
func (c *readdMICluster) flush(drop func(m *pb.Message) bool) {
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
		// A response from a member the recipient no longer tracks is dropped, as Node does.
		if err := c.nodes[m.GetTo()].rn.Step(m); err != nil && err != ErrStepPeerNotFound {
			c.t.Fatal(err)
		}
		if m.GetType() == pb.MessageType_MsgSnap {
			src.rn.ReportSnapshot(m.GetTo(), SnapshotFinish)
		}
	}
}

// TestTLATraceReaddedMemberHeartbeat runs three RawNodes, configured as tla/README.md's example,
// through a schedule where the leader removes a follower and adds it back, and validates the
// trace with tla/Traceetcdraft.tla as tla/validate.sh does. Every step is ordinary raft behavior
// (the member added back starts with a fresh progress, and its first heartbeat carries commit 0),
// yet TLC rejects the trace: the specification keeps the member's matchIndex from before the
// removal.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceReaddedMemberHeartbeat(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &readdMIRecorder{}
	c := &readdMICluster{t: t, nodes: map[uint64]*readdMINode{}}
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
		c.nodes[id] = &readdMINode{rn: rn, st: st}
	}
	none := func(*pb.Message) bool { return false }
	c.flush(none) // each node applies the bootstrap configuration
	leader := c.nodes[1]

	// Term 2: node 1 is elected and replicates an entry to both followers (index 5).
	if err := leader.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.flush(none)
	if err := leader.rn.Propose([]byte("a")); err != nil {
		t.Fatal(err)
	}
	c.flush(none)
	if pr, ok := leader.rn.Status().Progress[3]; !ok || pr.Match != 5 {
		t.Fatalf("leader's progress of node 3: %v, want match 5", pr)
	}

	// The leader removes node 3 (index 6), then adds it back (index 7); each change is committed
	// and applied before the next is proposed. The append the leader sends node 3 once it is
	// added back is lost.
	for k, typ := range []pb.ConfChangeType{pb.ConfChangeRemoveNode, pb.ConfChangeAddNode} {
		if err := leader.rn.ProposeConfChange(&pb.ConfChange{Type: typ.Enum(), NodeId: proto.Uint64(3)}); err != nil {
			t.Fatal(err)
		}
		c.flush(func(m *pb.Message) bool { return typ == pb.ConfChangeAddNode && m.GetTo() == 3 })
		_, has3 := leader.rn.Status().Progress[3]
		if want := typ == pb.ConfChangeAddNode; has3 != want || leader.applied != 6+uint64(k) {
			t.Fatalf("after %v 3: leader applied %d, has a progress of node 3: %v", typ, leader.applied, has3)
		}
	}
	if s := leader.rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetCommit() != 7 {
		t.Fatalf("node 1: %v commit %d, want leader with commit 7", s.RaftState, s.HardState.GetCommit())
	}
	if pr := leader.rn.Status().Progress[3]; pr.Match != 0 {
		t.Fatalf("leader's progress of node 3 added back: match %d, want 0", pr.Match)
	}

	// A heartbeat: to node 3 it carries commit min(Match, committed) = 0.
	leader.rn.Tick()
	c.ready(1)
	sawHeartbeat := false
	for _, m := range c.inflight {
		if m.GetType() == pb.MessageType_MsgHeartbeat && m.GetTo() == 3 {
			sawHeartbeat = true
			if m.GetCommit() != 0 {
				t.Fatalf("heartbeat to node 3: commit %d, want 0", m.GetCommit())
			}
		}
	}
	if !sawHeartbeat {
		t.Fatalf("no heartbeat 1->3")
	}
	// Node 3 answers, and the leader brings it up to date.
	c.flush(none)
	if pr := leader.rn.Status().Progress[3]; pr.Match != 7 {
		t.Fatalf("leader's progress of node 3: match %d, want 7", pr.Match)
	}
	if s := c.nodes[3].rn.BasicStatus(); s.HardState.GetCommit() != 7 {
		t.Fatalf("node 3: commit %d, want 7", s.HardState.GetCommit())
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
		for _, l := range readdMILines(out, "Error: ") {
			t.Log(l)
		}
		if n := readdMILastLine(out); n >= 1 && n <= len(rec.lines) {
			t.Logf("TLC matched lines 1-%d of %d; line %d: %s", n-1, len(rec.lines), n, rec.lines[n-1])
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func readdMILines(out []byte, prefix string) []string {
	var ls []string
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, prefix) {
			ls = append(ls, l)
		}
	}
	return ls
}

// readdMILastLine is the trace line TLC's counterexample stops at (the value of l in its last
// state), or 0.
func readdMILastLine(out []byte) int {
	n := 0
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, "/\\ l = ") {
			fmt.Sscanf(strings.TrimPrefix(l, "/\\ l = "), "%d", &n)
		}
	}
	return n
}
