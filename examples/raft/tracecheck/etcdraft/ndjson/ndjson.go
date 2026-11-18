// Package ndjson reads raft's traces in the format of its TLA+ trace validation (NDJSON, one
// event per line) into etcdraft's events, strictly where TLC would fail reading them. Not part of
// what is proved: the closed program converts raft's events in memory.
package ndjson

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"

	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
)

// ReadNDJSON reads a trace in the format of raft's trace validation: one JSON object per line,
// those with `"tag":"trace"` holding an event under `"event"` (`OriginTraceLog`). It is strict
// where TLC would fail reading the trace (a missing field): an event's objects must have exactly
// the keys raft's TracingEvent writes (case-sensitive), with the optional ones (msg, prop, and in
// a configuration change changes and newconf) possibly absent (prop's keys are free but for cc,
// the only one the specification reads), and a "trace" line must have an event. (So it rejects a few traces TLC would accept, those with a field TLC never reads missing
// or an extra one; raft never writes them.)
func ReadNDJSON(r io.Reader) ([]etcdraft.Event, error) {
	var out []etcdraft.Event
	sc := bufio.NewScanner(r)
	sc.Buffer(make([]byte, 1<<20), 1<<26)
	n := 0
	for sc.Scan() {
		n++
		line := sc.Bytes()
		if len(line) == 0 {
			continue
		}
		var rec map[string]json.RawMessage
		if err := json.Unmarshal(line, &rec); err != nil {
			return nil, fmt.Errorf("line %d: %w", n, err)
		}
		var tag string
		if raw, ok := rec["tag"]; ok {
			if err := json.Unmarshal(raw, &tag); err != nil {
				tag = ""
			}
		}
		if tag != "trace" {
			continue
		}
		raw, ok := rec["event"]
		if !ok {
			return nil, fmt.Errorf("line %d: a trace line without an event", n)
		}
		ev, err := decodeEvent(raw)
		if err != nil {
			return nil, fmt.Errorf("line %d: %w", n, err)
		}
		out = append(out, ev)
	}
	return out, sc.Err()
}

// exactKeys decodes raw, a JSON object, checking that it has every key of required and no key
// but those and optional's.
func exactKeys(raw json.RawMessage, what string, required, optional []string) (map[string]json.RawMessage, error) {
	var m map[string]json.RawMessage
	if err := json.Unmarshal(raw, &m); err != nil {
		return nil, fmt.Errorf("%s: %w", what, err)
	}
	allowed := map[string]bool{}
	for _, k := range required {
		if _, ok := m[k]; !ok {
			return nil, fmt.Errorf("%s: no field %q", what, k)
		}
		allowed[k] = true
	}
	for _, k := range optional {
		allowed[k] = true
	}
	for k := range m {
		if !allowed[k] {
			return nil, fmt.Errorf("%s: unknown field %q", what, k)
		}
	}
	return m, nil
}

// decodeEvent decodes a trace line's event, checking its objects' keys (ReadNDJSON).
func decodeEvent(raw json.RawMessage) (etcdraft.Event, error) {
	var ev etcdraft.Event
	m, err := exactKeys(raw, "event", []string{"name", "nid", "state", "role", "log", "conf"}, []string{"msg", "prop"})
	if err != nil {
		return ev, err
	}
	if _, err := exactKeys(m["state"], "state", []string{"term", "vote", "commit"}, nil); err != nil {
		return ev, err
	}
	var conf []json.RawMessage
	if err := json.Unmarshal(m["conf"], &conf); err != nil || len(conf) != 2 {
		return ev, fmt.Errorf("conf: not a pair of lists")
	}
	if raw, ok := m["msg"]; ok {
		if _, err := exactKeys(raw, "msg", []string{"type", "term", "from", "to", "entries", "logTerm", "index",
			"commit", "vote", "reject", "rejectHint"}, nil); err != nil {
			return ev, err
		}
	}
	if raw, ok := m["prop"]; ok {
		// prop holds what raft adds to an event (a configuration change's cc, a replication
		// message's match and next, ...); the specification reads only cc, whose shape is checked
		var pm map[string]json.RawMessage
		if err := json.Unmarshal(raw, &pm); err != nil {
			return ev, fmt.Errorf("prop: %w", err)
		}
		if cc, ok := pm["cc"]; ok {
			ccm, err := exactKeys(cc, "cc", nil, []string{"changes", "newconf"})
			if err != nil {
				return ev, err
			}
			if ch, ok := ccm["changes"]; ok {
				var changes []json.RawMessage
				if err := json.Unmarshal(ch, &changes); err != nil {
					return ev, fmt.Errorf("changes: %w", err)
				}
				for _, c := range changes {
					if _, err := exactKeys(c, "change", []string{"nid", "action"}, nil); err != nil {
						return ev, err
					}
				}
			}
		}
	}
	if err := json.Unmarshal(raw, &ev); err != nil {
		return ev, err
	}
	return ev, nil
}
