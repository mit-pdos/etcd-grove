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
	"testing"

	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// rcRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON
// line per event, the event in the "event" field), in the order raft emits them.
type rcRecorder struct{ lines [][]byte }

func (r *rcRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// TestTLATraceRestartWithoutSnapshot runs three RawNodes, configured as tla/README.md's example,
// elects node 1 and commits its entry on every node, then restarts node 2 from its storage (a new
// RawNode on the same MemoryStorage, as RestartNode does) before any snapshot: raft restores the
// storage's empty configuration and the application applies the committed configuration changes
// again. It validates the trace with tla/Traceetcdraft.tla as tla/validate.sh does. Every step is
// ordinary raft behavior, yet TLC rejects the trace at the restarted node's InitState line: the
// specification's Restart restores the configuration of the node's last Ready.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceRestartWithoutSnapshot(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &rcRecorder{}
	type node struct {
		rn        *RawNode
		st        *MemoryStorage
		confState *pb.ConfState
		applied   uint64
	}
	config := func(id uint64, st *MemoryStorage, applied uint64) *Config {
		return &Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st, Applied: applied,
			MaxSizePerMsg: 4096, MaxInflightMsgs: 256, TraceLogger: rec}
	}
	nodes := map[uint64]*node{}
	for id := uint64(1); id <= 3; id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(config(id, st, 0))
		if err != nil {
			t.Fatal(err)
		}
		if err := rn.Bootstrap([]Peer{{ID: 1}, {ID: 2}, {ID: 3}}); err != nil {
			t.Fatal(err)
		}
		nodes[id] = &node{rn: rn, st: st}
	}
	var inflight []*pb.Message
	// ready persists a Ready's entries and hard state, sends its messages and applies its
	// committed entries (the configuration changes through ApplyConfChange).
	ready := func(id uint64) {
		n := nodes[id]
		if !n.rn.HasReady() {
			return
		}
		rd := n.rn.Ready()
		if err := n.st.Append(rd.Entries); err != nil {
			t.Fatal(err)
		}
		if rd.HardState != nil && !IsEmptyHardState(rd.HardState) {
			if err := n.st.SetHardState(rd.HardState); err != nil {
				t.Fatal(err)
			}
		}
		inflight = append(inflight, rd.Messages...)
		for _, e := range rd.CommittedEntries {
			if e.GetType() == pb.EntryConfChange {
				cc := &pb.ConfChange{}
				if err := proto.Unmarshal(e.GetData(), cc); err != nil {
					t.Fatal(err)
				}
				n.confState = n.rn.ApplyConfChange(cc)
			}
			n.applied = e.GetIndex()
		}
		n.rn.Advance(rd)
	}
	deliver := func(from, to uint64, typ pb.MessageType) {
		for k, m := range inflight {
			if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
				inflight = append(inflight[:k], inflight[k+1:]...)
				if err := nodes[to].rn.Step(m); err != nil {
					t.Fatal(err)
				}
				return
			}
		}
		t.Fatalf("no %v %d->%d in flight", typ, from, to)
	}
	for id := uint64(1); id <= 3; id++ {
		ready(id)
	}

	// Term 2: node 1 is elected and replicates its empty entry at index 4 to nodes 2 and 3.
	if err := nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	ready(1)
	deliver(1, 2, pb.MessageType_MsgVote)
	deliver(1, 3, pb.MessageType_MsgVote)
	ready(2)
	ready(3)
	deliver(2, 1, pb.MessageType_MsgVoteResp)
	deliver(3, 1, pb.MessageType_MsgVoteResp)
	ready(1)
	deliver(1, 2, pb.MessageType_MsgApp)
	deliver(1, 3, pb.MessageType_MsgApp)
	ready(2)
	ready(3)
	deliver(2, 1, pb.MessageType_MsgAppResp)
	deliver(3, 1, pb.MessageType_MsgAppResp)
	ready(1)
	// A heartbeat tells nodes 2 and 3 that index 4 is committed.
	nodes[1].rn.Tick()
	ready(1)
	deliver(1, 2, pb.MessageType_MsgHeartbeat)
	deliver(1, 3, pb.MessageType_MsgHeartbeat)
	ready(2)
	ready(3)
	deliver(2, 1, pb.MessageType_MsgHeartbeatResp)
	deliver(3, 1, pb.MessageType_MsgHeartbeatResp)
	ready(1)

	// Node 2 restarts from its storage, as RestartNode does, before its application took any
	// snapshot (etcd's first snapshot comes after thousands of entries): raft restores the
	// storage's (empty) configuration, and the application applies the committed entries again,
	// the configuration changes through ApplyConfChange, from Config.Applied (0, what its
	// snapshot covers).
	n2 := nodes[2]
	if n2.applied != 4 {
		t.Fatalf("node 2 applied %d, want 4", n2.applied)
	}
	before := n2.rn.BasicStatus()
	rn, err := NewRawNode(config(2, n2.st, 0))
	if err != nil {
		t.Fatal(err)
	}
	n2.rn = rn
	n2.applied = 0
	after := n2.rn.BasicStatus()
	if after.HardState.GetTerm() != before.HardState.GetTerm() ||
		after.HardState.GetVote() != before.HardState.GetVote() ||
		after.HardState.GetCommit() != before.HardState.GetCommit() {
		t.Fatalf("node 2 restarted with %v, want its state before the restart %v", after.HardState, before.HardState)
	}
	ready(2)
	if n2.applied != 4 {
		t.Fatalf("node 2 applied %d after the restart, want 4", n2.applied)
	}
	if got := n2.rn.Status().Config.Voters[0].Slice(); len(got) != 3 {
		t.Fatalf("node 2 has voters %v after re-applying its log, want 1, 2, 3", got)
	}

	// The restarted node 2 answers node 1's next heartbeat.
	nodes[1].rn.Tick()
	ready(1)
	deliver(1, 2, pb.MessageType_MsgHeartbeat)
	ready(2)
	deliver(2, 1, pb.MessageType_MsgHeartbeatResp)
	ready(1)
	if s := nodes[1].rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetCommit() != 4 {
		t.Fatalf("node 1: %v commit %d, want leader with commit 4", s.RaftState, s.HardState.GetCommit())
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
		for _, l := range rcErrorLines(out, "Error: ") {
			t.Log(l)
		}
		if k := rcUnmatchedLine(out); k > 0 && k <= len(rec.lines) {
			t.Logf("no behavior matches trace line %d: %s", k, rec.lines[k-1])
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func rcErrorLines(out []byte, prefix string) []string {
	var ls []string
	start := 0
	for i, c := range out {
		if c == '\n' {
			if l := string(out[start:i]); len(l) >= len(prefix) && l[:len(prefix)] == prefix {
				ls = append(ls, l)
			}
			start = i + 1
		}
	}
	return ls
}

// rcUnmatchedLine is the trace line TLC's counterexample stops at: the largest value of
// Traceetcdraft's line counter l in its states (0 if none).
func rcUnmatchedLine(out []byte) int {
	k := 0
	for _, l := range rcErrorLines(out, "/\\ l = ") {
		var n int
		if _, err := fmt.Sscanf(l, "/\\ l = %d", &n); err == nil && n > k {
			k = n
		}
	}
	return k
}
