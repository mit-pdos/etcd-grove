// Package ndjson reads a stream of rawnode reports (one JSON object per line, as
// antithesis-fm/tracekit/go/sink.go writes them) into check.Events, as TraceKit's stream operator
// (antithesis-fm/tracekit/stream/TraceKit.java) turns each line into a TLA+ record: objects are
// records, arrays sequences, numbers integers, strings strings, null "".
//
// Not part of what the closed theorem's program runs (its harness builds the events in memory).
package ndjson

import (
	"bufio"
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math"
	"os"
	"strings"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
)

// ReadFile reads a stream file.
func ReadFile(path string) ([]*check.Event, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	return Read(f)
}

// Read reads a stream: one event per non-blank line.
func Read(r io.Reader) ([]*check.Event, error) {
	var out []*check.Event
	sc := bufio.NewScanner(r)
	sc.Buffer(make([]byte, 1<<20), 1<<28)
	for sc.Scan() {
		line := sc.Bytes()
		if len(bytes.TrimSpace(line)) == 0 {
			continue
		}
		ev, err := Parse(line)
		if err != nil {
			return nil, fmt.Errorf("line %d: %w", len(out)+1, err)
		}
		out = append(out, ev)
	}
	return out, sc.Err()
}

// Parse reads one line. A line that is not a JSON object is an error; a field of a kind the
// binding cannot read (a string where it reads a number, ...) makes the event Bad, an evaluation
// error when the checker reaches it.
func Parse(line []byte) (*check.Event, error) {
	var obj map[string]json.RawMessage
	d := json.NewDecoder(bytes.NewReader(line))
	d.UseNumber()
	if err := d.Decode(&obj); err != nil {
		return nil, err
	}
	ev := &check.Event{}
	p := parser{ev: ev}
	ev.E = p.str(obj, "e")
	ev.Node = p.str(obj, "node")
	for name, raw := range obj {
		switch name {
		case "by":
			ev.By = p.strv(raw, name)
			ev.Has |= check.FBy
		case "role":
			ev.Role = p.strv(raw, name)
			ev.Has |= check.FRole
		case "term":
			ev.Term = p.intv(raw, name)
			ev.Has |= check.FTerm
		case "vote":
			ev.Vote = p.strv(raw, name)
			ev.Has |= check.FVote
		case "commit":
			ev.Commit = p.intv(raw, name)
			ev.Has |= check.FCommit
		case "first":
			ev.First = p.intv(raw, name)
			ev.Has |= check.FFirst
		case "entries":
			ev.Entries = p.entries(raw, name)
			ev.Has |= check.FEntries
		case "lastIndex":
			ev.LastIdx = p.intv(raw, name)
			ev.Has |= check.FLastIndex
		case "lastTerm":
			ev.LastTerm = p.intv(raw, name)
			ev.Has |= check.FLastTerm
		case "applied":
			ev.Applied = p.intv(raw, name)
			ev.Has |= check.FApplied
		case "voters":
			ev.Voters = p.strs(raw, name)
			ev.Has |= check.FVoters
		case "outgoing":
			ev.Outgoing = p.strs(raw, name)
			ev.Has |= check.FOutgoing
		case "snap":
			var o map[string]json.RawMessage
			if p.obj(raw, name, &o) {
				ev.Snap = check.SnapRef{Index: p.intf(o, "index", "snap.index"), Term: p.intf(o, "term", "snap.term")}
			}
			ev.Has |= check.FSnap
		case "msg":
			ev.Msg = p.msg(raw, name)
			ev.Has |= check.FMsg
		case "cause":
			var arr []json.RawMessage
			if p.arr(raw, name, &arr) {
				for _, m := range arr {
					ev.Cause = append(ev.Cause, p.msg(m, "cause[]"))
				}
			}
			ev.Has |= check.FCause
		case "b":
			ev.Has |= check.FB
		case "a":
			ev.Has |= check.FA
		case "w":
			ev.W = p.intv(raw, name)
			ev.Has |= check.FW
		case "more":
			ev.More = p.intv(raw, name)
			ev.Has |= check.FMore
		case "index":
			ev.Index = p.intv(raw, name)
			ev.Has |= check.FIndex
		case "ctx":
			ev.Ctx = p.strv(raw, name)
			ev.Has |= check.FCtx
		}
	}
	if p.bad != "" {
		ev.Bad = p.bad
	}
	return ev, nil
}

type parser struct {
	ev  *check.Event
	bad string
}

func (p *parser) fail(what string) {
	if p.bad == "" {
		p.bad = what
	}
}

func isNull(raw json.RawMessage) bool { return strings.TrimSpace(string(raw)) == "null" }

func (p *parser) str(obj map[string]json.RawMessage, name string) string {
	raw, ok := obj[name]
	if !ok {
		p.fail("no field " + name)
		return ""
	}
	return p.strv(raw, name)
}

func (p *parser) strv(raw json.RawMessage, name string) string {
	if isNull(raw) {
		return ""
	}
	var s string
	if err := json.Unmarshal(raw, &s); err != nil {
		p.fail(name + ": not a string")
	}
	return s
}

func (p *parser) intv(raw json.RawMessage, name string) int {
	var n json.Number
	d := json.NewDecoder(bytes.NewReader(raw))
	d.UseNumber()
	if err := d.Decode(&n); err != nil {
		p.fail(name + ": not a number")
		return 0
	}
	i, err := n.Int64()
	// TraceKit.java: getAsInt (a 32-bit integer).
	if err != nil || i > math.MaxInt32 || i < math.MinInt32 {
		p.fail(name + ": not a 32-bit integer")
		return 0
	}
	return int(i)
}

func (p *parser) intf(obj map[string]json.RawMessage, name, what string) int {
	raw, ok := obj[name]
	if !ok {
		p.fail("no field " + what)
		return 0
	}
	return p.intv(raw, what)
}

func (p *parser) boolf(obj map[string]json.RawMessage, name, what string) bool {
	raw, ok := obj[name]
	if !ok {
		p.fail("no field " + what)
		return false
	}
	var b bool
	if err := json.Unmarshal(raw, &b); err != nil {
		p.fail(what + ": not a boolean")
	}
	return b
}

func (p *parser) strf(obj map[string]json.RawMessage, name, what string) string {
	raw, ok := obj[name]
	if !ok {
		p.fail("no field " + what)
		return ""
	}
	return p.strv(raw, what)
}

func (p *parser) obj(raw json.RawMessage, name string, o *map[string]json.RawMessage) bool {
	if err := json.Unmarshal(raw, o); err != nil || *o == nil {
		p.fail(name + ": not an object")
		return false
	}
	return true
}

func (p *parser) arr(raw json.RawMessage, name string, a *[]json.RawMessage) bool {
	if err := json.Unmarshal(raw, a); err != nil {
		p.fail(name + ": not an array")
		return false
	}
	return true
}

func (p *parser) strs(raw json.RawMessage, name string) []string {
	var arr []json.RawMessage
	if !p.arr(raw, name, &arr) {
		return nil
	}
	var out []string
	for _, r := range arr {
		out = append(out, p.strv(r, name+"[]"))
	}
	return out
}

func (p *parser) entries(raw json.RawMessage, name string) []check.Entry {
	var arr []json.RawMessage
	if !p.arr(raw, name, &arr) {
		return nil
	}
	var out []check.Entry
	for _, r := range arr {
		var o map[string]json.RawMessage
		if !p.obj(r, "entry", &o) {
			continue
		}
		e := check.Entry{Term: p.intf(o, "term", "entry.term"), Type: p.strf(o, "type", "entry.type")}
		v, ok := o["value"]
		if !ok {
			p.fail("no field entry.value")
		} else if strings.HasPrefix(strings.TrimSpace(string(v)), "{") {
			var c map[string]json.RawMessage
			if p.obj(v, "entry.value", &c) {
				e.Value = check.Value{IsRec: true,
					Add:    p.strs(c["add"], "value.add"),
					Remove: p.strs(c["remove"], "value.remove"),
					Joint:  p.boolf(c, "joint", "value.joint"),
					Leave:  p.boolf(c, "leave", "value.leave")}
			}
		} else {
			e.Value = check.Value{Str: p.strv(v, "entry.value")}
		}
		out = append(out, e)
	}
	return out
}

func (p *parser) msg(raw json.RawMessage, name string) check.Msg {
	var o map[string]json.RawMessage
	if !p.obj(raw, name, &o) {
		return check.Msg{}
	}
	m := check.Msg{
		Type:    p.strf(o, "type", "msg.type"),
		From:    p.strf(o, "from", "msg.from"),
		To:      p.strf(o, "to", "msg.to"),
		Term:    p.intf(o, "term", "msg.term"),
		Index:   p.intf(o, "index", "msg.index"),
		LogTerm: p.intf(o, "logTerm", "msg.logTerm"),
		Commit:  p.intf(o, "commit", "msg.commit"),
		Reject:  p.boolf(o, "reject", "msg.reject"),
		Hint:    p.intf(o, "hint", "msg.hint"),
	}
	if e, ok := o["entries"]; ok {
		m.Entries = p.entries(e, "msg.entries")
	} else {
		p.fail("no field msg.entries")
	}
	return m
}
