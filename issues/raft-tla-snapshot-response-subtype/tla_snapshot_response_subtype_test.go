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

// snapRSRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON line
// per event, the event in the "event" field), in the order raft emits them.
type snapRSRecorder struct{ lines [][]byte }

func (r *snapRSRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// snapRSNode is one member: its RawNode, its storage, and what its application has applied.
type snapRSNode struct {
	rn      *RawNode
	st      *MemoryStorage
	applied uint64
	cs      *pb.ConfState
	// snapOnConf: after applying a configuration change, the application snapshots what it
	// applied and compacts its log (as etcd's snapshots include the latest configuration).
	snapOnConf bool
}

// snapRSCluster is RawNodes 1..n and the messages in flight between them, delivered by the
// test.
type snapRSCluster struct {
	t        *testing.T
	nodes    map[uint64]*snapRSNode
	inflight []*pb.Message
}

// ready handles id's Ready as an application does: installs the snapshot, persists the entries
// and hard state, sends the messages, applies the committed entries (configuration changes
// through ApplyConfChange), and advances.
func (c *snapRSCluster) ready(id uint64) {
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
	confApplied := false
	for _, e := range rd.CommittedEntries {
		if e.GetType() == pb.EntryConfChange {
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(e.GetData(), cc); err != nil {
				t.Fatal(err)
			}
			n.cs = n.rn.ApplyConfChange(cc)
			confApplied = true
		}
		n.applied = e.GetIndex()
	}
	if confApplied && n.snapOnConf {
		if _, err := n.st.CreateSnapshot(n.applied, n.cs, nil); err != nil {
			t.Fatal(err)
		}
		if err := n.st.Compact(n.applied); err != nil {
			t.Fatal(err)
		}
	}
	n.rn.Advance(rd)
}

// flush handles every node's Ready and delivers the messages in flight in the order they were
// sent, until none is left; a message for which drop holds is lost (and reported unreachable,
// as etcd's transport does).
func (c *snapRSCluster) flush(drop func(m *pb.Message) bool) {
	for {
		for id := uint64(1); id <= uint64(len(c.nodes)); id++ {
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

// TestTLATraceSnapshotToNewMember runs three RawNodes, configured as tla/README.md's example,
// adds a fourth member with an empty log, which the leader brings up to date with a snapshot, and
// validates the trace with tla/Traceetcdraft.tla as tla/validate.sh does. Every step is ordinary
// raft behavior (the new member installs the snapshot and answers with MsgAppResp), yet TLC
// rejects the trace: the specification answers a snapshot with a response of subtype "snapshot",
// which no MsgAppResp matches.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceSnapshotToNewMember(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &snapRSRecorder{}
	c := &snapRSCluster{t: t, nodes: map[uint64]*snapRSNode{}}
	for id := uint64(1); id <= 4; id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(&Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
			MaxSizePerMsg: 4096, MaxInflightMsgs: 256, TraceLogger: rec})
		if err != nil {
			t.Fatal(err)
		}
		// Nodes 1-3 are the initial members; node 4 starts empty, to join later (as a member
		// added at runtime starts, with no bootstrap).
		if id <= 3 {
			if err := rn.Bootstrap([]Peer{{ID: 1}, {ID: 2}, {ID: 3}}); err != nil {
				t.Fatal(err)
			}
		}
		c.nodes[id] = &snapRSNode{rn: rn, st: st}
	}
	none := func(*pb.Message) bool { return false }
	c.flush(none) // each initial member applies the bootstrap configuration
	leader := c.nodes[1]
	leader.snapOnConf = true

	// Term 2: node 1 is elected; it adds node 4 (index 5) and, once that is applied, snapshots
	// index 5 (configuration {1, 2, 3, 4}) and compacts its log, so node 4 gets the snapshot.
	if err := leader.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.flush(none)
	if err := leader.rn.ProposeConfChange(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: proto.Uint64(4)}); err != nil {
		t.Fatal(err)
	}
	c.flush(none)

	sawSnap := false
	for _, l := range rec.lines {
		if strings.Contains(string(l), `"type":"MsgSnap","term":2,"from":"1","to":"4"`) {
			sawSnap = true
		}
	}
	if !sawSnap {
		t.Fatalf("no MsgSnap 1->4 in the trace")
	}
	n4 := c.nodes[4]
	if s := n4.rn.BasicStatus(); s.HardState.GetCommit() != 5 || n4.applied != 5 {
		t.Fatalf("node 4: commit %d applied %d, want the snapshot at 5 installed", s.HardState.GetCommit(), n4.applied)
	}
	if snap, err := n4.st.Snapshot(); err != nil || snap.GetMetadata().GetIndex() != 5 {
		t.Fatalf("node 4's storage: snapshot %v (%v), want index 5", snap.GetMetadata(), err)
	}
	if pr := leader.rn.Status().Progress[4]; pr.Match != 5 {
		t.Fatalf("leader's progress of node 4: match %d, want 5", pr.Match)
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
		for _, l := range snapRSLines(out, "Error: ") {
			t.Log(l)
		}
		if n := snapRSLastLine(out); n >= 1 && n <= len(rec.lines) {
			t.Logf("TLC matched lines 1-%d of %d; line %d: %s", n-1, len(rec.lines), n, rec.lines[n-1])
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func snapRSLines(out []byte, prefix string) []string {
	var ls []string
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, prefix) {
			ls = append(ls, l)
		}
	}
	return ls
}

// snapRSLastLine is the trace line TLC's counterexample stops at (the value of l in its last
// state), or 0.
func snapRSLastLine(out []byte) int {
	n := 0
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, "/\\ l = ") {
			fmt.Sscanf(strings.TrimPrefix(l, "/\\ l = "), "%d", &n)
		}
	}
	return n
}
