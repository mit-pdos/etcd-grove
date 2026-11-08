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
	"regexp"
	"strconv"
	"strings"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// lcRecorder logs every TracingEvent as tla/README.md's example logger does (one JSON line per
// event, the event in the "event" field), in the order raft emits them.
type lcRecorder struct{ lines [][]byte }

func (r *lcRecorder) TraceEvent(ev *TracingEvent) {
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
	out, err := lcValidate(t)
	if err != nil {
		for _, l := range lcErrorLines(out) {
			t.Log(l)
		}
		t.Fatalf("Traceetcdraft rejects the trace of a correct raft run: %v", err)
	}
}

// TestTLAModelStaleLeaderCompleteness shows that etcdraft.tla itself, not only raft, reaches a
// state violating LeaderCompletenessInv: it replays the states of TLC's counterexample (the
// specification's variables, without the trace's l and pl) against MCetcdraft.tla alone, from
// its Init, each step required to be a NextAsync step (a disjunct of Next) or a stutter landing exactly on the
// next recorded state (lcReplay), within MCetcdraft.cfg's limits.
func TestTLAModelStaleLeaderCompleteness(t *testing.T) {
	out, err := lcValidate(t)
	if err == nil || !strings.Contains(string(out), "Invariant LeaderCompletenessInv is violated") {
		t.Fatalf("trace validation did not report LeaderCompletenessInv violated (err %v)", err)
	}
	if n := lcReplay(t, out, []string{"1", "2", "3"}, "LeaderCompletenessInv"); n > 0 {
		t.Fatalf("etcdraft.tla itself (from MCetcdraft's Init, %d steps of NextAsync or stutter) reaches a state violating LeaderCompletenessInv", n-1)
	}
}

// lcValidate runs the schedule and validates its trace with TLC, returning TLC's output.
func lcValidate(t *testing.T) ([]byte, error) {
	tools := os.Getenv("TLA_TOOLS")
	if tools == "" {
		t.Skip("TLA_TOOLS not set")
	}
	rec := &lcRecorder{}
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
	return lcTLC(t, "Traceetcdraft", "Traceetcdraft", lcSpecDir(t), dir, "JSON="+trace)
}

// lcSpecDir is the module's tla/ directory.
func lcSpecDir(t *testing.T) string {
	spec, err := filepath.Abs("tla")
	if err != nil {
		t.Fatal(err)
	}
	return spec
}

// lcTLC runs TLC on module.tla with config.cfg in dir, as tla/validate.sh does.
func lcTLC(t *testing.T, module, config, dir, meta string, env ...string) ([]byte, error) {
	tools := os.Getenv("TLA_TOOLS")
	cmd := exec.Command("java", "-XX:+UseParallelGC",
		"-cp", filepath.Join(tools, "tla2tools.jar")+":"+filepath.Join(tools, "CommunityModules-deps.jar"),
		"tlc2.TLC", "-config", config+".cfg", module+".tla", "-lncheck", "final",
		"-metadir", filepath.Join(meta, "state-"+module))
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), env...)
	return cmd.CombinedOutput()
}

func lcErrorLines(out []byte) []string {
	var ls []string
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, "Error: ") {
			ls = append(ls, l)
		}
	}
	return ls
}

var lcVar = regexp.MustCompile(`^/\\ (\w+) = (.*)$`)
var lcK = regexp.MustCompile(`/\\ k = (\d+)`)

// lcReplay takes TLC's first error trace in out (Traceetcdraft's counterexample), keeps the
// specification's variables of each state, and checks with TLC that MCetcdraft.tla alone produces
// that sequence: Init, then each step a NextAsync step (Next without its crash and network-fault disjuncts, which no recorded step
// takes; evaluating Restart fails in some reachable states: raft-tla-restart-truncated-log) or a stutter
// onto the next recorded state, with
// deadlock checking on (a step the specification cannot take stops the replay there). The
// recorded bootstrap entries (the trace specification's, each with the whole configuration) are
// replaced by MCetcdraft's BootstrapLog (one server added per entry). It returns the number of
// states replayed when TLC reports inv violated at the last of them, 0 if it does not.
func lcReplay(t *testing.T, out []byte, servers []string, inv string) int {
	var states []map[string]string
	var cur map[string]string
	var last string
	in := false
	for _, l := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(l, "<<\"Progress %:\"") {
			continue
		}
		if strings.HasPrefix(l, "Error: The behavior up to this point is:") {
			in = true
			continue
		}
		if !in {
			continue
		}
		if strings.HasPrefix(l, "Error:") {
			break
		}
		if strings.HasPrefix(l, "State ") {
			cur = map[string]string{}
			states = append(states, cur)
			continue
		}
		if cur == nil || strings.TrimSpace(l) == "" {
			continue
		}
		if m := lcVar.FindStringSubmatch(l); m != nil {
			last = m[1]
			cur[last] = m[2]
		} else {
			cur[last] += "\n" + l
		}
	}
	if len(states) == 0 {
		t.Fatal("no error trace in TLC's output")
	}
	var names []string
	for n := range states[0] {
		if n != "l" && n != "pl" {
			names = append(names, n)
		}
	}
	lcSortStrings(names)
	var b strings.Builder
	b.WriteString("---- MODULE Replay ----\nEXTENDS MCetcdraft, TLC, Sequences\nVARIABLE k\n")
	b.WriteString("Fix(lg) == [j \\in DOMAIN lg |-> IF j <= Len(BootstrapLog) THEN BootstrapLog[j] ELSE lg[j]]\n")
	b.WriteString("S(r) == [r EXCEPT !.log = [i \\in DOMAIN r.log |-> Fix(r.log[i])]]\nRaw == <<\n")
	for si, st := range states {
		if si > 0 {
			b.WriteString(",\n")
		}
		b.WriteString("[ ")
		for ni, n := range names {
			v, ok := st[n]
			if !ok {
				t.Fatalf("state %d lacks %s", si+1, n)
			}
			if ni > 0 {
				b.WriteString(",\n  ")
			}
			b.WriteString(n + " |-> " + v)
		}
		b.WriteString(" ]")
	}
	b.WriteString("\n>>\nStates == [n \\in 1..Len(Raw) |-> S(Raw[n])]\nCur == [ ")
	for ni, n := range names {
		if ni > 0 {
			b.WriteString(", ")
		}
		b.WriteString(n + " |-> " + n)
	}
	b.WriteString(" ]\nRInit == /\\ Init /\\ k = 1 /\\ Cur = States[1]\n")
	b.WriteString("RNext == /\\ k < Len(States)\n         /\\ \\/ NextAsync\n            \\/ UNCHANGED vars\n")
	b.WriteString("         /\\ Cur' = States[k + 1]\n         /\\ k' = k + 1\n")
	b.WriteString("RSpec == RInit /\\ [][RNext]_<<vars, k>>\n====\n")
	q := make([]string, len(servers))
	for i, s := range servers {
		q[i] = strconv.Quote(s)
	}
	set := "{" + strings.Join(q, ", ") + "}"
	mcLimits := "    Timeout         <- MCTimeout\n    Send            <- MCSend\n    ClientRequest   <- MCClientRequest\n"
	run := func(limits string) (int, int) {
		cfg := `SPECIFICATION RSpec
CONSTANTS
    InitServer = ` + set + `
    Server     = ` + set + `
    Nil = "0"
    ValueEntry  = "ValueEntry"
    ConfigEntry = "ConfigEntry"
    Follower    = "StateFollower"
    Candidate   = "StateCandidate"
    Leader      = "StateLeader"
    RequestVoteRequest      =   "RequestVoteRequest"
    RequestVoteResponse     =   "RequestVoteResponse"
    AppendEntriesRequest    =   "AppendEntriesRequest"
    AppendEntriesResponse   =   "AppendEntriesResponse"
    InitServerVars  <- etcdInitServerVars
    InitLogVars     <- etcdInitLogVars
    InitConfigVars  <- etcdInitConfigVars
` + limits + `    ReconfigurationLimit    = 2
    MaxTermLimit            = 10
    RequestLimit            = 5
CHECK_DEADLOCK TRUE
INVARIANT
    ` + inv + "\n"
		dir := t.TempDir()
		ents, err := os.ReadDir(lcSpecDir(t))
		if err != nil {
			t.Fatal(err)
		}
		for _, e := range ents {
			if strings.HasSuffix(e.Name(), ".tla") && !strings.Contains(e.Name(), "_TTrace_") {
				src, err := os.ReadFile(filepath.Join(lcSpecDir(t), e.Name()))
				if err != nil {
					t.Fatal(err)
				}
				if err := os.WriteFile(filepath.Join(dir, e.Name()), src, 0o644); err != nil {
					t.Fatal(err)
				}
			}
		}
		if err := os.WriteFile(filepath.Join(dir, "Replay.tla"), []byte(b.String()), 0o644); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, "Replay.cfg"), []byte(cfg), 0o644); err != nil {
			t.Fatal(err)
		}
		rout, _ := lcTLC(t, "Replay", "Replay", dir, dir)
		rs := string(rout)
		for _, l := range lcErrorLines(rout) {
			t.Log("replay" + map[bool]string{true: " (MCetcdraft's limits)", false: ""}[limits != ""] + ": " + l)
		}
		ks := lcK.FindAllStringSubmatch(rs, -1)
		n := 0
		if len(ks) > 0 {
			n, _ = strconv.Atoi(ks[len(ks)-1][1])
		}
		if !strings.Contains(rs, "Invariant "+inv+" is violated") || n != len(states) {
			return 0, n
		}
		return len(states), n
	}
	full, _ := run("")
	if mc, at := run(mcLimits); mc > 0 {
		t.Logf("replay: also within MCetcdraft.cfg's limits (MCTimeout, MCSend, MCClientRequest)")
	} else {
		t.Logf("replay: not within MCetcdraft.cfg's limits (MCTimeout, MCSend, MCClientRequest): stops at state %d of %d", at, len(states))
	}
	return full
}

func lcSortStrings(s []string) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j] < s[j-1]; j-- {
			s[j], s[j-1] = s[j-1], s[j]
		}
	}
}
