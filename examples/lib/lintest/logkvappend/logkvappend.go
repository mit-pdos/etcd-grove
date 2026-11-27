// Package logkvappend is logkv (examples/lib/lintest/logkv) with a second kind of write, Append,
// which appends to the register's value: the log's entries say which kind they are. Its feature
// in the experiment: a new operation, and a new field in the log's entries.
package logkvappend

import (
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// An Op is an operation's input: a write of Val (Put), an append of Val (Append), or a read.
type Op struct {
	Put    bool
	Append bool
	Val    string
}

// Model is the register's sequential specification: the state is a string, initially empty; a
// write sets it, an append appends to it, both output the empty string; a read outputs it.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return "" },
		Step: func(state, input, output any) (bool, any) {
			s := state.(string)
			in := input.(Op)
			if in.Put {
				return true, in.Val
			}
			if in.Append {
				return true, s + in.Val
			}
			return output.(string) == s, s
		},
		Equal: func(a, b any) bool { return a.(string) == b.(string) },
	}
}

// An entry is a write in the log: of val, or (app) an append of val.
type entry struct {
	app bool
	val string
}

// A Server holds the log of writes, how many of them are applied, and the applied state, under
// one mutex. The condition variable is signaled when the log grows or entries are applied.
type Server struct {
	mu      sync.Mutex
	cond    *sync.Cond
	log     []entry
	applied uint64
	state   string
}

// New returns a server with an empty log and starts its apply goroutine.
func New() *Server {
	s := &Server{}
	s.cond = sync.NewCond(&s.mu)
	go s.applyLoop()
	return s
}

// applyLoop applies the log's entries in order, forever: it sets the state to each write's value,
// or appends an append's, and wakes the waiting writers, then waits for more entries.
func (s *Server) applyLoop() {
	s.mu.Lock()
	for {
		for s.applied < uint64(len(s.log)) {
			e := s.log[s.applied]
			if e.app {
				s.state = s.state + e.val
			} else {
				s.state = e.val
			}
			s.applied = s.applied + 1
		}
		s.cond.Broadcast()
		s.cond.Wait()
	}
}

// write appends e to the log and returns once the apply goroutine has applied it.
func (s *Server) write(e entry) {
	s.mu.Lock()
	s.log = append(s.log, e)
	idx := uint64(len(s.log))
	s.cond.Broadcast()
	for s.applied < idx {
		s.cond.Wait()
	}
	s.mu.Unlock()
}

// Put writes v: it returns once the write is applied.
func (s *Server) Put(v string) {
	s.write(entry{app: false, val: v})
}

// Append appends v to the value: it returns once the append is applied.
func (s *Server) Append(v string) {
	s.write(entry{app: true, val: v})
}

// Get returns the applied state.
func (s *Server) Get() string {
	s.mu.Lock()
	v := s.state
	s.mu.Unlock()
	return v
}

// Apply runs one operation: a write returns the empty string, a read the value read.
func (s *Server) Apply(input any) any {
	in := input.(Op)
	if in.Put {
		s.Put(in.Val)
		return ""
	}
	if in.Append {
		s.Append(in.Val)
		return ""
	}
	return s.Get()
}

// Check runs clients clients of a fresh server, each running ops operations, each at random a
// write, an append or a read of one of eight values, traced with the given clock, and checks the
// trace with porcupine.
func Check(clock lintest.Clock, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	s := New()
	vals := []string{"a", "b", "c", "d", "e", "f", "g", "h"}
	gen := func(id int) any {
		k := primitive.RandomUint64() % 3
		return Op{Put: k == 0, Append: k == 1, Val: vals[primitive.RandomUint64()%8]}
	}
	return lintest.Run(Model(), s.Apply, gen, clock, clients, ops, timeout)
}

// MaxClients and MaxOps cap Main's random workload: it runs between 1 and MaxClients clients of
// between 1 and MaxOps operations each, well within Run's bounds (clients < 2^31,
// clients*ops < 2^60).
const (
	MaxClients = 8
	MaxOps     = 32
)

// Main runs a random number of clients (at most MaxClients), each running a random number of
// random operations (at most MaxOps) against the server, traced with a counter clock, checks the
// trace with porcupine (no timeout), and panics unless porcupine answers Ok.
func Main() {
	clients := 1 + int(primitive.RandomUint64()%MaxClients)
	ops := 1 + int(primitive.RandomUint64()%MaxOps)
	if r := Check(lintest.CounterClock(), clients, ops, 0); r != porcupine.Ok {
		panic("porcupine rejected a linearizable register's trace")
	}
}
