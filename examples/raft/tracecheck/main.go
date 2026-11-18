//go:build with_tla || goose

package tracecheck

import (
	"go.etcd.io/raft/v3"

	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
)

// Main is the closed program (notes/trace-validation-plan.md): it runs a concurrent cluster of
// DefaultCConfig (its random choices primitive.RandomUint64's), then checks its trace against
// raft's TLA+ trace specification (etcdraft.CheckTrace, with the invariants), and panics unless
// TLC would accept it (TLCOK: matched, the search never branched, no invariant violated, no
// evaluation error).
func Main() {
	c, err := RunConcurrent(DefaultCConfig())
	if err != nil {
		panic("tracecheck: the cluster did not start")
	}
	tr, err := etcdraft.NewTrace(ConvertEvents(c.Events()))
	if err != nil {
		panic("tracecheck: the trace is not one the specification reads")
	}
	if !etcdraft.CheckTrace(tr, true).TLCOK() {
		panic("tracecheck: the trace does not pass raft's TLA+ trace validation")
	}
}

// ConvertEvents is raft's events as the checker reads them: what their NDJSON (WriteNDJSON, the
// format of raft's trace validation) reads as through ndjson.ReadNDJSON, without the JSON. The
// fields JSON omits when empty (raft's omitempty: the message, the properties, a configuration
// change's change list and new configuration) are absent (nil) when empty here too; of the
// properties, only the configuration change (cc) is kept, the only one the specification reads.
func ConvertEvents(events []raft.TracingEvent) []etcdraft.Event {
	out := make([]etcdraft.Event, len(events))
	for k := range events {
		ev := &events[k]
		out[k] = etcdraft.Event{
			Name:  ev.Name,
			NID:   ev.NodeID,
			State: etcdraft.EventState{Term: int(ev.State.Term), Vote: ev.State.Vote, Commit: int(ev.State.Commit)},
			Role:  ev.Role,
			Log:   int(ev.LogSize),
			Conf:  [2][]string{ev.Conf[0], ev.Conf[1]},
		}
		if m := ev.Message; m != nil {
			out[k].Msg = &etcdraft.EventMsg{Type: m.Type, Term: int(m.Term), From: m.From, To: m.To,
				Entries: m.EntryLength, LogTerm: int(m.LogTerm), Index: int(m.Index), Commit: int(m.Commit),
				Vote: m.Vote, Reject: m.Reject, RejectHint: int(m.RejectHint)}
		}
		if len(ev.Properties) != 0 {
			props := &etcdraft.EventProps{}
			if cc, ok := ev.Properties["cc"].(*raft.TracingConfChange); ok && cc != nil {
				ecc := &etcdraft.EventConfChange{}
				if len(cc.Changes) != 0 {
					changes := make([]etcdraft.EventChange, len(cc.Changes))
					for h, c := range cc.Changes {
						changes[h] = etcdraft.EventChange{NID: c.NodeID, Action: c.Action}
					}
					ecc.Changes = &changes
				}
				if len(cc.NewConf) != 0 {
					newconf := append([]string(nil), cc.NewConf...)
					ecc.NewConf = &newconf
				}
				props.CC = ecc
			}
			out[k].Prop = props
		}
	}
	return out
}
