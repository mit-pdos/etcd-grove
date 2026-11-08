package etcdraft

import (
	"strings"
	"testing"
)

// The cases where TLC stops with an evaluation error, or fails reading the trace, and the
// transcription must not accept (the review of 2026-11-08, notes/raft-trace-validation.md).

// ev is a trace line, in raft's format, of an event of node 1 with the given state and extra
// fields (JSON, after the conf).
func ev(name, state, extra string) string {
	return `{"tag":"trace","event":{"name":"` + name + `","nid":"1","state":` + state +
		`,"role":"StateFollower","log":3,"conf":[["1"],[]]` + extra + `}}`
}

const st = `{"term":1,"vote":"0","commit":3}`

func readTrace(lines ...string) ([]Event, error) {
	return ReadNDJSON(strings.NewReader(strings.Join(lines, "\n") + "\n"))
}

// A plain two-line trace (bootstrap, then a Ready) is accepted: the cases below change one thing.
func TestStrictBaseline(t *testing.T) {
	events, err := readTrace(ev("InitState", st, ""), ev("Ready", st, ""))
	if err != nil {
		t.Fatal(err)
	}
	tr, err := NewTrace(events)
	if err != nil {
		t.Fatal(err)
	}
	if r := CheckTrace(tr, true); !r.TLCOK() {
		t.Fatalf("baseline: %v", r)
	}
}

// A commit index beyond the log: TLC fails evaluating Committed (SubSeq past the log's end) in
// LogInv; the reviewer's witness w3/commit.ndjson.
func TestCommitBeyondLog(t *testing.T) {
	events, err := readTrace(ev("InitState", `{"term":1,"vote":"0","commit":4}`, ""), ev("Ready", st, ""))
	if err != nil {
		t.Fatal(err)
	}
	tr, err := NewTrace(events)
	if err != nil {
		t.Fatal(err)
	}
	r := CheckTrace(tr, true)
	if r.OK || r.EvalError == "" {
		t.Fatalf("want an evaluation error, got %v", r)
	}
}

// Fields TLC reads by name: a key in another case, a missing key, an unknown key, and a trace line
// without an event are rejected (Go's encoding/json alone matches keys case-insensitively and
// reads a missing one as zero; the reviewer's witness w4/case.ndjson).
func TestStrictJSON(t *testing.T) {
	for name, bad := range map[string]string{
		"key case":        ev("Ready", `{"TERM":1,"vote":"0","commit":3}`, ""),
		"missing key":     ev("Ready", `{"vote":"0","commit":3}`, ""),
		"unknown key":     ev("Ready", `{"term":1,"vote":"0","commit":3,"lead":"1"}`, ""),
		"no event":        `{"tag":"trace","msg":"trace"}`,
		"conf not a pair": strings.Replace(ev("Ready", st, ""), `[["1"],[]]`, `[["1"]]`, 1),
		"msg missing key": ev("SendAppendEntriesRequest", st, `,"msg":{"type":"MsgApp","term":1,"from":"1","to":"2"}`),
	} {
		if _, err := readTrace(ev("InitState", st, ""), bad); err == nil {
			t.Errorf("%s: accepted", name)
		}
	}
}

// An id not in canonical form ("01"): TLA+ compares the strings, so it is not server "1".
func TestNonCanonicalID(t *testing.T) {
	events, err := readTrace(ev("InitState", st, ""), strings.Replace(ev("Ready", st, ""), `"nid":"1"`, `"nid":"01"`, 1))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := NewTrace(events); err == nil {
		t.Fatal("accepted")
	}
}

// A server's last bootstrap line an ApplyConfChange without newconf (raft omits an empty one):
// TLC fails reading prop.cc.newconf in BootstrappedConfig; the reviewer's witness w1/nobf.ndjson.
func TestMissingNewconf(t *testing.T) {
	events, err := readTrace(ev("InitState", st, ""), ev("ApplyConfChange", st, `,"prop":{"cc":{}}`), ev("Ready", st, ""))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := NewTrace(events); err == nil {
		t.Fatal("accepted")
	}
}

// A message event without its message: TLC fails reading logline.event.msg.
func TestMessageEventWithoutMsg(t *testing.T) {
	events, err := readTrace(ev("InitState", st, ""), ev("SendAppendEntriesRequest", st, ""))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := NewTrace(events); err == nil {
		t.Fatal("accepted")
	}
}

// Role strings other than the three are distinct values, as in TLA+ (the reviewer's witness
// w2/roles.ndjson: "StateA" and "StateB" compared equal).
func TestDistinctRoles(t *testing.T) {
	if ParseRole("StateA") == ParseRole("StateB") || ParseRole("StatePreCandidate") == Candidate {
		t.Fatal("distinct role strings compare equal")
	}
	if ParseRole("StateLeader") != Leader {
		t.Fatal("StateLeader is not Leader")
	}
}

// The search branching is detected (TLC's TraceMatched fails then): node 1, the leader, receives a
// heartbeat response from node 2 that two messages in transit match, differing only in their
// mmatchIndex (which LoglineIsAppendEntriesResponse does not check of a heartbeat's), so the two
// receipts give two states.
func TestBranchingDetected(t *testing.T) {
	line := func(nid, name, extra string) string {
		return `{"tag":"trace","event":{"name":"` + name + `","nid":"` + nid + `","state":{"term":1,"vote":"0","commit":0},"role":"StateFollower","log":0,"conf":[["1","2"],[]]` + extra + `}}`
	}
	events, err := readTrace(line("1", "InitState", ""), line("2", "InitState", ""),
		line("1", "ReceiveAppendEntriesResponse", `,"msg":{"type":"MsgHeartbeatResp","term":1,"from":"2","to":"1","entries":0,"logTerm":0,"index":0,"commit":0,"vote":"0","reject":false,"rejectHint":0}`))
	if err != nil {
		t.Fatal(err)
	}
	tr, err := NewTrace(events)
	if err != nil {
		t.Fatal(err)
	}
	s := tr.Init().S.clone()
	s.mut(1).State = Leader
	for _, match := range []int{0, 5} {
		s.Messages = s.Messages.With(&Msg{Type: AppendEntriesResponse, Subtype: "heartbeat", Term: 1, Success: true,
			MatchIndex: match, Source: 2, Dest: 1})
	}
	succ, info := tr.StepLine(TState{S: s, L: 3, PL: 3}, false)
	if len(succ) != 2 || !info.Branched {
		t.Fatalf("want two successors and a branch, got %d, branched %t", len(succ), info.Branched)
	}
}
