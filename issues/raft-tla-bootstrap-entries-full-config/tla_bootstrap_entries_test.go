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

type bcRecorder struct{ lines [][]byte }

func (r *bcRecorder) TraceEvent(ev *TracingEvent) {
	b, err := json.Marshal(ev)
	if err != nil {
		panic(err)
	}
	r.lines = append(r.lines, []byte(fmt.Sprintf(`{"level":"debug","ts":%d,"msg":"trace","tag":"trace","event":%s}`,
		1_000_000_000+len(r.lines), b)))
}

// TestTLATraceBootstrapEntriesOneByOne runs three bootstrapped RawNodes and a fourth with an empty
// log, with MaxSizePerMsg 1 (one entry per append request, and so one committed entry per
// Ready), adds the fourth as a voter, and validates the trace with tla/Traceetcdraft.tla as
// tla/validate.sh does. The new member receives the bootstrap log one entry at a time and applies
// its three ConfChangeAddNode entries one at a time (configurations {1}, {1, 2}, {1, 2, 3}), as
// raft intends; the trace specification gives every bootstrap entry the whole configuration
// {1, 2, 3}, so TLC rejects the trace at the new member's first receipt after applying entry 1.
//
// It needs TLA_TOOLS, a directory with tla2tools.jar and CommunityModules-deps.jar (what
// validate.sh downloads), and java.
func TestTLATraceBootstrapEntriesOneByOne(t *testing.T) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &bcRecorder{}
	type node struct {
		rn *RawNode
		st *MemoryStorage
	}
	nodes := map[uint64]*node{}
	for id := uint64(1); id <= 4; id++ {
		st := NewMemoryStorage()
		rn, err := NewRawNode(&Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
			MaxSizePerMsg: 1, MaxInflightMsgs: 256, TraceLogger: rec})
		if err != nil {
			t.Fatal(err)
		}
		if id <= 3 {
			if err := rn.Bootstrap([]Peer{{ID: 1}, {ID: 2}, {ID: 3}}); err != nil {
				t.Fatal(err)
			}
		}
		nodes[id] = &node{rn: rn, st: st}
	}
	var inflight []*pb.Message
	var confs4 []string // node 4's configuration after each configuration change it applies
	ready := func(id uint64) {
		n := nodes[id]
		rd := n.rn.Ready()
		if err := n.st.Append(rd.Entries); err != nil {
			t.Fatal(err)
		}
		if rd.HardState != nil && !IsEmptyHardState(rd.HardState) {
			if err := n.st.SetHardState(rd.HardState); err != nil {
				t.Fatal(err)
			}
		}
		for _, m := range rd.Messages {
			inflight = append(inflight, proto.Clone(m).(*pb.Message))
		}
		for _, e := range rd.CommittedEntries {
			if e.GetType() == pb.EntryConfChange {
				cc := &pb.ConfChange{}
				if err := proto.Unmarshal(e.GetData(), cc); err != nil {
					t.Fatal(err)
				}
				cs := n.rn.ApplyConfChange(cc)
				if id == 4 {
					confs4 = append(confs4, fmt.Sprint(cs.GetVoters()))
				}
			}
		}
		n.rn.Advance(rd)
	}
	// flush handles every Ready and delivers every message in the order sent, until none is left.
	flush := func() {
		for {
			busy := false
			for id := uint64(1); id <= 4; id++ {
				if nodes[id].rn.HasReady() {
					ready(id)
					busy = true
				}
			}
			if len(inflight) > 0 {
				m := inflight[0]
				inflight = inflight[1:]
				if err := nodes[m.GetTo()].rn.Step(m); err != nil {
					t.Fatal(err)
				}
				continue
			}
			if !busy {
				return
			}
		}
	}
	flush()
	if err := nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	flush()
	if err := nodes[1].rn.ProposeConfChange(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: proto.Uint64(4)}); err != nil {
		t.Fatal(err)
	}
	flush()
	nodes[1].rn.Tick()
	flush()

	if got := strings.Join(confs4, " "); got != "[1] [1 2] [1 2 3] [1 2 3 4]" {
		t.Fatalf("node 4 applied configurations %s, want [1] [1 2] [1 2 3] [1 2 3 4]", got)
	}
	if s := nodes[4].rn.BasicStatus(); s.HardState.GetCommit() != 5 {
		t.Fatalf("node 4: commit %d, want 5", s.HardState.GetCommit())
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
		k := 0
		for _, l := range strings.Split(string(out), "\n") {
			if strings.HasPrefix(l, "Error: ") {
				t.Log(l)
			}
			var n int
			if _, e := fmt.Sscanf(l, "/\\ l = %d", &n); e == nil && n > k {
				k = n
			}
		}
		if k > 0 && k <= len(rec.lines) {
			t.Logf("no behavior matches trace line %d: %s", k, rec.lines[k-1])
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}
