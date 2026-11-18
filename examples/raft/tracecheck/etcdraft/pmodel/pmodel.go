// Package pmodel is the trace specification (package etcdraft) as a porcupine model: a cross-check
// of the direct checker, outside what is proved (notes/trace-validation-plan.md). It also has a
// canonical encoding of states (Key), for porcupine's hashing and for the state-space test.
package pmodel

import (
	"fmt"
	"hash/fnv"
	"sort"
	"strings"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
)

func writeEntry(b *strings.Builder, e etcdraft.Entry) {
	fmt.Fprintf(b, "(%d,%d,%d,%d,%v,%v)", e.Term, e.Type, e.Value.Kind, e.Value.Val, []uint64(e.Value.NewConf), []uint64(e.Value.Learners))
}

// MsgKey is a canonical encoding of m: two messages are equal exactly when their keys are.
func MsgKey(m *etcdraft.Msg) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%d|%s|%d|%d|%d|%t|%d|%d|%d|%t|%d|%d|%d|", m.Type, m.Subtype, m.Term, m.LastLogTerm,
		m.LastLogIndex, m.VoteGranted, m.PrevLogIndex, m.PrevLogTerm, m.CommitIndex, m.Success, m.MatchIndex,
		m.Source, m.Dest)
	for _, e := range m.Entries {
		writeEntry(&b, e)
	}
	return b.String()
}

func bagKey(sb *strings.Builder, bag etcdraft.Bag) {
	var keys []string
	count := map[string]int{}
	for _, m := range bag.Domain() {
		k := MsgKey(m)
		keys = append(keys, k)
		count[k] = bag.Count(m)
	}
	sort.Strings(keys)
	for _, k := range keys {
		fmt.Fprintf(sb, "[%s]x%d;", k, count[k])
	}
}

// Key is a canonical encoding of s: two states are Equal exactly when their keys are.
func Key(s *etcdraft.State) string {
	var b strings.Builder
	for _, i := range s.Server {
		v := s.S[i]
		fmt.Fprintf(&b, "%d:%d,%q,%d,%d,%d,%v,%v,", i, v.CurrentTerm, string(v.State), v.VotedFor, v.Lead, v.CommitIndex,
			[]uint64(v.VotesResponded), []uint64(v.VotesGranted))
		for _, j := range s.Server {
			fmt.Fprintf(&b, "%d.", v.MatchIndex[j])
		}
		fmt.Fprintf(&b, ",%d,%v%v%v,", v.PendingConfChangeIndex, []uint64(v.Config.Joint[0]), []uint64(v.Config.Joint[1]),
			[]uint64(v.Config.Learners))
		d := v.Durable
		fmt.Fprintf(&b, "%d,%d,%d,%v%v%v,", d.CurrentTerm, d.VotedFor, d.CommitIndex,
			[]uint64(d.Config.Joint[0]), []uint64(d.Config.Joint[1]), []uint64(d.Config.Learners))
		for _, e := range d.Log {
			writeEntry(&b, e)
		}
		b.WriteString("|")
		for _, e := range v.Log {
			writeEntry(&b, e)
		}
		b.WriteString(";")
	}
	fmt.Fprintf(&b, "rc%d;M", s.ReconfigCount)
	bagKey(&b, s.Messages)
	b.WriteString(";P")
	bagKey(&b, s.PendingMessages)
	return b.String()
}

// pstate is a porcupine state of Model: a trace-specification state with its key cached.
type pstate struct {
	ts  etcdraft.TState
	key string
}

func newPState(ts etcdraft.TState) *pstate {
	return &pstate{ts: ts, key: fmt.Sprint(ts.L) + "#" + Key(ts.S)}
}

// Model is the trace specification of t as a porcupine NondeterministicModel: an operation is a
// line of the trace (its input the line number l, its output unused), and a state of the model is
// a state of the trace specification at that line; Step is StepLine (every state at line l+1). A
// line from a state where an invariant is violated (when invariants is set) or an evaluation fails
// has no successor. Porcupine's acceptance is "some path matches" (Result.OK), not TLC's stricter
// TraceMatched (Result.TLCOK); with a search that never branches they are the same.
func Model(t *etcdraft.Trace, invariants bool) porcupine.NondeterministicModel {
	return porcupine.NondeterministicModel{
		Init: func() []interface{} {
			return []interface{}{newPState(t.Init())}
		},
		Step: func(state, input, output interface{}) (out []interface{}) {
			// An evaluation TLC would fail, or an invariant violated by any state reached
			// (intermediate steps included), fails the line: porcupine then answers Illegal, as
			// TLC reports an error. (A state that violates no invariant is not filtered out: a
			// violation is a failure, not a dead end.)
			defer func() {
				if x := recover(); x != nil {
					if _, ok := x.(etcdraft.EvalError); !ok {
						panic(x)
					}
					out = nil
				}
			}()
			ps := state.(*pstate)
			l := input.(int)
			if ps.ts.L != l {
				return nil
			}
			succ, info := t.StepLine(ps.ts, invariants)
			if info.Violation != "" {
				return nil
			}
			for _, s2 := range succ {
				out = append(out, newPState(s2))
			}
			return out
		},
		Equal: func(a, b interface{}) bool { return a.(*pstate).key == b.(*pstate).key },
		Hash: func(state interface{}) uint64 {
			h := fnv.New64a()
			h.Write([]byte(state.(*pstate).key))
			return h.Sum64()
		},
		DescribeOperation: func(input, output interface{}) string {
			l := input.(int)
			ev := t.Event(l)
			return fmt.Sprintf("%d: %s %s", l, ev.Name, ev.NID)
		},
		DescribeState: func(state interface{}) string { return state.(*pstate).ts.S.String() },
	}
}

// History is t as a porcupine history: line l is the operation with input l, called at 2l and
// returning at 2l+1 (so the lines are totally ordered: porcupine's only linearization is the
// trace's order).
func History(t *etcdraft.Trace) []porcupine.Operation {
	ops := make([]porcupine.Operation, t.Len())
	for l := 1; l <= t.Len(); l++ {
		ops[l-1] = porcupine.Operation{ClientId: 0, Input: l, Output: nil, Call: int64(2 * l), Return: int64(2*l + 1)}
	}
	return ops
}

// CheckPorcupine checks t with porcupine (CheckOperationsTimeout of Model's ToModel on History).
func CheckPorcupine(t *etcdraft.Trace, invariants bool, timeout time.Duration) porcupine.CheckResult {
	m := Model(t, invariants)
	return porcupine.CheckOperationsTimeout(m.ToModel(), History(t), timeout)
}
