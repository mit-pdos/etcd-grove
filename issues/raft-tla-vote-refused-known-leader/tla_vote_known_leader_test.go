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

// voteKnownLeaderRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON
// line per event, the event in the "event" field), in the order raft emits them.
type voteKnownLeaderRecorder struct{ lines [][]byte }

func (r *voteKnownLeaderRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// TestTLATraceVoteRefusedKnownLeader runs three RawNodes, configured as tla/README.md's example
// (no CheckQuorum, no PreVote), through a schedule in which a follower learns its term's leader
// from a heartbeat before the leader's own (delayed) MsgVote reaches it, and validates the trace
// with tla/Traceetcdraft.tla as tla/validate.sh does. The follower refuses the vote, as raft does
// for any vote request in a term whose leader it knows, yet the specification grants it, and TLC
// rejects the trace.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceVoteRefusedKnownLeader(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &voteKnownLeaderRecorder{}
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
	for id := uint64(1); id <= 3; id++ {
		ready(id)
	}

	// Term 2: node 1 is elected with node 2's vote; its MsgVote to node 3 is delayed.
	if err := nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	ready(1)
	deliver(1, 2, pb.MessageType_MsgVote)
	ready(2)
	deliver(2, 1, pb.MessageType_MsgVoteResp)
	ready(1) // the MsgApps of node 1's empty entry stay in flight

	// Node 3 learns of leader 1 of term 2 from its first heartbeat, without having voted.
	nodes[1].rn.Tick()
	ready(1)
	deliver(1, 3, pb.MessageType_MsgHeartbeat)
	ready(3)

	// The delayed MsgVote of term 2 arrives: node 3 refuses it, as it would any candidate's.
	deliver(1, 3, pb.MessageType_MsgVote)
	ready(3)
	resp := take(3, 1, pb.MessageType_MsgVoteResp)
	if !resp.GetReject() || resp.GetTerm() != 2 {
		t.Fatalf("node 3's MsgVoteResp: term %d reject %v, want a refusal in term 2", resp.GetTerm(), resp.GetReject())
	}
	if s := nodes[3].rn.BasicStatus(); s.Lead != 1 || s.HardState.GetTerm() != 2 || s.HardState.GetVote() != None {
		t.Fatalf("node 3: lead %d term %d vote %d, want lead 1 in term 2 with no vote", s.Lead, s.HardState.GetTerm(), s.HardState.GetVote())
	}
	if err := nodes[1].rn.Step(resp); err != nil {
		t.Fatal(err)
	}
	ready(1)
	if s := nodes[1].rn.BasicStatus(); s.RaftState != StateLeader || s.HardState.GetTerm() != 2 {
		t.Fatalf("node 1: %v term %d, want leader of term 2", s.RaftState, s.HardState.GetTerm())
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
		for _, l := range voteKnownLeaderErrorLines(out, "Error: ") {
			t.Log(l)
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

func voteKnownLeaderErrorLines(out []byte, prefix string) []string {
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
