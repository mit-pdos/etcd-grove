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

// tlaDemoteRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON
// line per event, the event in the "event" field), in the order raft emits them.
type tlaDemoteRecorder struct{ lines [][]byte }

func (r *tlaDemoteRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// TestTLATraceLearnerDemotion runs three RawNodes, configured as tla/README.md's example, elects
// node 1, and has it demote voter 3 to a learner (ConfChangeAddLearnerNode of a voter, which
// raft accepts); the change commits and every node applies it. It validates the trace with
// tla/Traceetcdraft.tla as tla/validate.sh does. Every step is ordinary raft behavior, yet TLC
// rejects the trace at the leader's ChangeConf line.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceLearnerDemotion(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &tlaDemoteRecorder{}
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
	// ready persists a Ready's entries and hard state, sends its messages and applies its
	// committed configuration changes through ApplyConfChange.
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
				n.rn.ApplyConfChange(cc)
			}
		}
		n.rn.Advance(rd)
	}
	// settle handles every node's Ready and delivers every message, in the order sent, until
	// none is left.
	settle := func() {
		for {
			for id := uint64(1); id <= 3; id++ {
				ready(id)
			}
			if len(inflight) == 0 {
				return
			}
			m := inflight[0]
			inflight = inflight[1:]
			if err := nodes[m.GetTo()].rn.Step(m); err != nil {
				t.Fatal(err)
			}
		}
	}
	settle()

	// Term 2: node 1 is elected and commits its empty entry at index 4.
	if err := nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	settle()
	if s := nodes[1].rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetCommit() != 4 {
		t.Fatalf("node 1: %v commit %d, want leader with commit 4", s.RaftState, s.HardState.GetCommit())
	}

	// Node 1 demotes voter 3 to a learner; the change commits at index 5 and every node applies it.
	cc := &pb.ConfChange{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: proto.Uint64(3)}
	if err := nodes[1].rn.ProposeConfChange(cc); err != nil {
		t.Fatal(err)
	}
	settle()
	for id := uint64(1); id <= 3; id++ {
		s := nodes[id].rn.Status()
		voters, learners := s.Config.Voters[0].Slice(), s.Config.Learners
		_, isLearner := learners[3]
		if s.HardState.GetCommit() != 5 || len(voters) != 2 || voters[0] != 1 || voters[1] != 2 ||
			len(learners) != 1 || !isLearner {
			t.Fatalf("node %d: commit %d, voters %v, learners %v; want commit 5, voters 1 2, learner 3",
				id, s.HardState.GetCommit(), voters, learners)
		}
	}
	if s := nodes[1].rn.BasicStatus(); s.RaftState != StateLeader {
		t.Fatalf("node 1: %v, want leader", s.RaftState)
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
		for _, l := range tlaDemoteErrorLines(out, "Error: ") {
			t.Log(l)
		}
		if k := tlaDemoteUnmatchedLine(out); k > 0 && k <= len(rec.lines) {
			t.Logf("no behavior matches trace line %d: %s", k, rec.lines[k-1])
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func tlaDemoteErrorLines(out []byte, prefix string) []string {
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

// tlaDemoteUnmatchedLine is the trace line TLC's counterexample stops at: the largest value of
// Traceetcdraft's line counter l in its states (0 if none).
func tlaDemoteUnmatchedLine(out []byte) int {
	k := 0
	for _, l := range tlaDemoteErrorLines(out, "/\\ l = ") {
		var n int
		if _, err := fmt.Sscanf(l, "/\\ l = %d", &n); err == nil && n > k {
			k = n
		}
	}
	return k
}
