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

	pb "go.etcd.io/raft/v3/raftpb"
)

// tlaRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON line per
// event, the event in the "event" field), in the order raft emits them.
type tlaRecorder struct{ lines [][]byte }

func (r *tlaRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// TestTLATraceStaleLeaderCompleteness runs three RawNodes, configured as tla/README.md's example
// (no CheckQuorum), through a schedule that leaves a stale leader, and validates the trace with
// tla/Traceetcdraft.tla as tla/validate.sh does. Every step is ordinary raft behavior, yet TLC
// reports "Invariant LeaderCompletenessInv is violated".
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceStaleLeaderCompleteness(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &tlaRecorder{}
	type node struct {
		rn *RawNode
		st *MemoryStorage
	}
	nodes := map[uint64]*node{}
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
		nodes[id] = &node{rn, st}
	}
	var inflight []*pb.Message
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
		n.rn.Advance(rd)
		inflight = append(inflight, rd.Messages...)
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
	lose := func() { inflight = nil }
	for id := uint64(1); id <= 3; id++ {
		ready(id)
	}

	// Term 2: node 1 is elected; its empty entry at index 4 (term 2) reaches no one.
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
	lose()

	// Term 3: node 2 is elected with node 3's vote and appends its own entry at index 4 (term 3).
	// Nothing it hears afterwards carries a later term, so it stays leader of term 3.
	if err := nodes[2].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	ready(2)
	deliver(2, 1, pb.MessageType_MsgVote)
	deliver(2, 3, pb.MessageType_MsgVote)
	ready(1)
	ready(3)
	deliver(3, 2, pb.MessageType_MsgVoteResp)
	lose()
	ready(2)
	lose()

	// Term 4: node 1 is elected with node 3's vote and replicates indexes 4 (term 2) and 5
	// (term 4) to node 3, committing 5 and with it 4.
	if err := nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	ready(1)
	deliver(1, 3, pb.MessageType_MsgVote)
	lose()
	ready(3)
	deliver(3, 1, pb.MessageType_MsgVoteResp)
	ready(1)
	deliver(1, 3, pb.MessageType_MsgApp) // rejected: node 3 has no index 4 of term 2
	lose()
	ready(3)
	deliver(3, 1, pb.MessageType_MsgAppResp)
	ready(1)
	deliver(1, 3, pb.MessageType_MsgApp) // indexes 4 and 5
	lose()
	ready(3)
	deliver(3, 1, pb.MessageType_MsgAppResp)
	ready(1)

	if s := nodes[1].rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetCommit() != 5 {
		t.Fatalf("node 1: %v commit %d, want leader with commit 5", s.RaftState, s.HardState.GetCommit())
	}
	if s := nodes[2].rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetTerm() != 3 {
		t.Fatalf("node 2: %v term %d, want leader of term 3", s.RaftState, s.HardState.GetTerm())
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
		for _, l := range regexpLines(out, "Error: ") {
			t.Log(l)
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func regexpLines(out []byte, prefix string) []string {
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
