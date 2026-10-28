// Package logkvsnap is logkv (examples/lintest/logkv) with the applied state as an immutable
// snapshot object that the apply goroutine replaces at each entry: readers take the current
// snapshot under the lock and read it after unlocking. Its feature in the experiment: state that
// Go replaces rather than mutates.
package logkvsnap

import (
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// An Op is an operation's input: a write of Val, or a read.
type Op struct {
	Put bool
	Val string
}

// Model is the register's sequential specification: the state is a string, initially empty; a
// write sets it and outputs the empty string, a read outputs it.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return "" },
		Step: func(state, input, output any) (bool, any) {
			s := state.(string)
			in := input.(Op)
			if in.Put {
				return true, in.Val
			}
			return output.(string) == s, s
		},
		Equal: func(a, b any) bool { return a.(string) == b.(string) },
	}
}

// A snapshot is the applied state after the first index writes; never changed once published.
type snapshot struct {
	val   string
	index uint64
}

// A Server holds the log of writes and the current snapshot, under one mutex. The condition
// variable is signaled when the log grows or entries are applied.
type Server struct {
	mu   sync.Mutex
	cond *sync.Cond
	log  []string
	snap *snapshot
}

// New returns a server with an empty log and starts its apply goroutine.
func New() *Server {
	s := &Server{snap: &snapshot{}}
	s.cond = sync.NewCond(&s.mu)
	go s.applyLoop()
	return s
}

// applyLoop applies the log's entries in order, forever: for each entry it publishes a new
// snapshot, then wakes the waiting writers and waits for more entries.
func (s *Server) applyLoop() {
	s.mu.Lock()
	for {
		for s.snap.index < uint64(len(s.log)) {
			i := s.snap.index
			s.snap = &snapshot{val: s.log[i], index: i + 1}
		}
		s.cond.Broadcast()
		s.cond.Wait()
	}
}

// Put appends a write of v to the log and returns once the apply goroutine has applied it.
func (s *Server) Put(v string) {
	s.mu.Lock()
	s.log = append(s.log, v)
	idx := uint64(len(s.log))
	s.cond.Broadcast()
	for s.snap.index < idx {
		s.cond.Wait()
	}
	s.mu.Unlock()
}

// Get returns the applied state: it takes the current snapshot under the lock and reads it
// after unlocking.
func (s *Server) Get() string {
	s.mu.Lock()
	sn := s.snap
	s.mu.Unlock()
	return sn.val
}

// Apply runs one operation: a write returns the empty string, a read the value read.
func (s *Server) Apply(input any) any {
	in := input.(Op)
	if in.Put {
		s.Put(in.Val)
		return ""
	}
	return s.Get()
}

// Check runs clients clients of a fresh server, each running ops operations (client i writes a
// value of its own if i is even and reads otherwise), traced with the given clock, and checks the
// trace with porcupine.
func Check(clock lintest.Clock, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	s := New()
	vals := []string{"a", "b", "c", "d"}
	gen := func(id int) any { return Op{Put: id%2 == 0, Val: vals[id%4]} }
	return lintest.Run(Model(), s.Apply, gen, clock, clients, ops, timeout)
}

// Main runs 4 clients of 10 operations each against the server, traced with a counter clock,
// checks the trace with porcupine (no timeout), and panics unless porcupine answers Ok.
func Main() {
	if r := Check(lintest.CounterClock(), 4, 10, 0); r != porcupine.Ok {
		panic("porcupine rejected a linearizable register's trace")
	}
}
