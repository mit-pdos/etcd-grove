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

// msgAppCommitRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON
// line per event, the event in the "event" field), in the order raft emits them.
type msgAppCommitRecorder struct{ lines [][]byte }

func (r *msgAppCommitRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// TestTLATraceMsgAppCommitBeyondEntries runs three RawNodes, configured as tla/README.md's example
// but with MaxSizePerMsg small enough that every MsgApp carries one entry, through a schedule in
// which the leader sends a lagging follower a MsgApp that stops short of the leader's commit
// index, and validates the trace with tla/Traceetcdraft.tla as tla/validate.sh does. Every step is
// ordinary raft behavior (the follower commits only up to the last entry it received), yet TLC
// rejects the trace.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceMsgAppCommitBeyondEntries(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &msgAppCommitRecorder{}
	type node struct {
		rn *RawNode
		st *MemoryStorage
	}
	nodes := map[uint64]*node{}
	for id := uint64(1); id <= 3; id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(&Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
			MaxSizePerMsg: 1, MaxCommittedSizePerReady: 1 << 20, MaxInflightMsgs: 256, TraceLogger: rec})
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
	// take removes the first message from -> to of type typ from the network.
	take := func(from, to uint64, typ pb.MessageType) *pb.Message {
		for k, m := range inflight {
			if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
				inflight = append(inflight[:k], inflight[k+1:]...)
				return m
			}
		}
		t.Fatalf("no %v %d->%d in flight", typ, from, to)
		return nil
	}
	deliver := func(from, to uint64, typ pb.MessageType) {
		if err := nodes[to].rn.Step(take(from, to, typ)); err != nil {
			t.Fatal(err)
		}
	}
	// deliverAll delivers every message from -> to of type typ, in the order sent.
	deliverAll := func(from, to uint64, typ pb.MessageType) {
		var rest, sel []*pb.Message
		for _, m := range inflight {
			if m.GetFrom() == from && m.GetTo() == to && m.GetType() == typ {
				sel = append(sel, m)
			} else {
				rest = append(rest, m)
			}
		}
		inflight = rest
		for _, m := range sel {
			if err := nodes[to].rn.Step(m); err != nil {
				t.Fatal(err)
			}
		}
	}
	for id := uint64(1); id <= 3; id++ {
		ready(id)
	}

	// Term 2: node 1 is elected with both votes and appends its empty entry at index 4.
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
	take(1, 3, pb.MessageType_MsgApp) // lost: node 3 falls behind

	// Node 2 receives index 4, then indexes 5 and 6, one per MsgApp; node 1 commits 6.
	deliver(1, 2, pb.MessageType_MsgApp)
	ready(2)
	deliver(2, 1, pb.MessageType_MsgAppResp)
	ready(1)
	for _, v := range []string{"a", "b"} {
		if err := nodes[1].rn.Propose([]byte(v)); err != nil {
			t.Fatal(err)
		}
	}
	ready(1)
	deliverAll(1, 2, pb.MessageType_MsgApp)
	ready(2)
	deliverAll(2, 1, pb.MessageType_MsgAppResp)
	ready(1)
	if c := nodes[1].rn.BasicStatus().HardState.GetCommit(); c != 6 {
		t.Fatalf("node 1: commit %d, want 6", c)
	}

	// Node 3 answers a heartbeat; node 1 resends from index 4, one entry, with its commit index 6.
	nodes[1].rn.Tick()
	ready(1)
	deliver(1, 3, pb.MessageType_MsgHeartbeat)
	ready(3)
	deliver(3, 1, pb.MessageType_MsgHeartbeatResp)
	ready(1)
	app := take(1, 3, pb.MessageType_MsgApp)
	if last := app.GetIndex() + uint64(len(app.GetEntries())); last != 4 || app.GetCommit() != 6 {
		t.Fatalf("MsgApp 1->3 carries up to index %d with commit %d, want 4 with commit 6", last, app.GetCommit())
	}
	if err := nodes[3].rn.Step(app); err != nil {
		t.Fatal(err)
	}
	ready(3)
	// The follower clamps: it commits only what it holds.
	if s := nodes[3].rn.BasicStatus(); s.HardState.GetCommit() != 4 {
		t.Fatalf("node 3: commit %d, want 4", s.HardState.GetCommit())
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
		for _, l := range msgAppCommitErrorLines(out, "Error: ") {
			t.Log(l)
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func msgAppCommitErrorLines(out []byte, prefix string) []string {
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
