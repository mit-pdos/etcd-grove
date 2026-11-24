package ndjson

import (
	"encoding/json"
	"io"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
)

// Write writes events as rawnode's reports, one JSON object per line (the inverse of Read on the
// fields the binding reads), for checking a stream with TLC (streamcheck.py).
func Write(w io.Writer, evs []*check.Event) error {
	enc := json.NewEncoder(w)
	for _, ev := range evs {
		if err := enc.Encode(toMap(ev)); err != nil {
			return err
		}
	}
	return nil
}

func entries(es []check.Entry) []map[string]any {
	out := []map[string]any{}
	for _, e := range es {
		var v any = e.Value.Str
		if e.Value.IsRec {
			v = map[string]any{"add": nonNil(e.Value.Add), "remove": nonNil(e.Value.Remove),
				"joint": e.Value.Joint, "leave": e.Value.Leave}
		}
		out = append(out, map[string]any{"term": e.Term, "type": e.Type, "value": v})
	}
	return out
}

func nonNil(s []string) []string {
	if s == nil {
		return []string{}
	}
	return s
}

func msg(m check.Msg) map[string]any {
	o := map[string]any{}
	if m.Has&check.MFType != 0 {
		o["type"] = m.Type
	}
	if m.Has&check.MFFrom != 0 {
		o["from"] = m.From
	}
	if m.Has&check.MFTo != 0 {
		o["to"] = m.To
	}
	if m.Has&check.MFTerm != 0 {
		o["term"] = m.Term
	}
	if m.Has&check.MFIndex != 0 {
		o["index"] = m.Index
	}
	if m.Has&check.MFLogTerm != 0 {
		o["logTerm"] = m.LogTerm
	}
	if m.Has&check.MFEntries != 0 {
		o["entries"] = entries(m.Entries)
	}
	if m.Has&check.MFCommit != 0 {
		o["commit"] = m.Commit
	}
	if m.Has&check.MFReject != 0 {
		o["reject"] = m.Reject
	}
	o["hint"] = m.Hint
	return o
}

func toMap(ev *check.Event) map[string]any {
	o := map[string]any{"e": ev.E, "node": ev.Node}
	h := func(f uint32) bool { return ev.Has&f != 0 }
	if h(check.FBy) {
		o["by"] = ev.By
	}
	if h(check.FRole) {
		o["role"] = ev.Role
	}
	if h(check.FTerm) {
		o["term"] = ev.Term
	}
	if h(check.FVote) {
		o["vote"] = ev.Vote
	}
	if h(check.FCommit) {
		o["commit"] = ev.Commit
	}
	if h(check.FFirst) {
		o["first"] = ev.First
	}
	if h(check.FEntries) {
		o["entries"] = entries(ev.Entries)
	}
	if h(check.FLastIndex) {
		o["lastIndex"] = ev.LastIdx
	}
	if h(check.FLastTerm) {
		o["lastTerm"] = ev.LastTerm
	}
	if h(check.FApplied) {
		o["applied"] = ev.Applied
	}
	if h(check.FVoters) {
		o["voters"] = nonNil(ev.Voters)
	}
	if h(check.FOutgoing) {
		o["outgoing"] = nonNil(ev.Outgoing)
	}
	if h(check.FSnap) {
		o["snap"] = map[string]any{"index": ev.Snap.Index, "term": ev.Snap.Term}
	}
	if h(check.FMsg) {
		o["msg"] = msg(ev.Msg)
	}
	if h(check.FCause) {
		cs := []map[string]any{}
		for _, m := range ev.Cause {
			cs = append(cs, msg(m))
		}
		o["cause"] = cs
	}
	if h(check.FB) {
		o["b"] = 1
	}
	if h(check.FA) {
		o["a"] = 1
	}
	if h(check.FW) {
		o["w"] = ev.W
	}
	if h(check.FMore) {
		o["more"] = ev.More
	}
	if h(check.FIndex) {
		o["index"] = ev.Index
	}
	if h(check.FCtx) {
		o["ctx"] = ev.Ctx
	}
	return o
}
