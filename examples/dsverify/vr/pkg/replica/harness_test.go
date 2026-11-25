package replica

// A deterministic harness for the replica's correctness tests: three replicas driven through
// Submit and Run over a fake network that records every event sent (encoded and decoded with
// the events package, as the TCP network does); the test chooses which recorded events are
// delivered, dropped or held, and in which order, and controls time with a virtual clock.

import (
	"bytes"
	"fmt"
	"io"
	"log/slog"
	"testing"

	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
	"github.com/tangledbytes/go-vsr/pkg/log"
	vsrtime "github.com/tangledbytes/go-vsr/pkg/time"
)

var memberAddrs = []string{"127.0.0.1:7001", "127.0.0.1:7002", "127.0.0.1:7003"}

// hb is the replicas' heartbeat timeout in ticks of the virtual clock.
const hb = 100

// msg is an event sent by replica from to the address to.
type msg struct {
	from int
	to   string
	ev   events.Event
}

func (m msg) String() string {
	return fmt.Sprintf("%d->%s %d %+v", m.from, m.to, m.ev.Type, m.ev.Data)
}

type fakeNet struct {
	c  *cluster
	id int
}

func (n *fakeNet) Send(to ipv4port.IPv4Port, f func(io.Writer) error) error {
	var buf bytes.Buffer
	if err := f(&buf); err != nil {
		return err
	}
	var ev events.Event
	if err := ev.FromReader(&buf); err != nil {
		n.c.t.Fatalf("an event sent does not decode: %v", err)
	}
	m := msg{from: n.id, to: to.String(), ev: ev}
	if n.c.replicaAt(m.to) >= 0 {
		n.c.pending = append(n.c.pending, m)
	} else {
		n.c.replies = append(n.c.replies, m)
	}
	return nil
}

func (n *fakeNet) Recv() (events.NetworkEvent, bool) { return events.NetworkEvent{}, false }

type cluster struct {
	t     *testing.T
	clock *vsrtime.Virtual
	reps  []*Replica
	addrs []ipv4port.IPv4Port
	// pending holds the events sent to replicas and not yet delivered or dropped, in order.
	pending []msg
	// replies holds the events sent to clients.
	replies []msg
	// executed[i] is the sequence of ops replica i's service executed (op k at index k-1).
	executed [][]string
}

func newCluster(t *testing.T) *cluster {
	c := &cluster{t: t, clock: vsrtime.NewVirtual(1)}
	for i := range memberAddrs {
		i := i
		var a ipv4port.IPv4Port
		if err := a.FromHostPort(memberAddrs[i]); err != nil {
			t.Fatal(err)
		}
		c.addrs = append(c.addrs, a)
		c.executed = append(c.executed, nil)
		r, err := New(Config{
			HeartbeatTimeout: hb,
			SrvHandler: func(op string) string {
				c.executed[i] = append(c.executed[i], op)
				return "res " + op
			},
			Network: &fakeNet{c: c, id: i},
			Time:    c.clock,
			ID:      uint64(i),
			Members: memberAddrs,
			Logger:  slog.New(slog.DiscardHandler),
		})
		if err != nil {
			t.Fatal(err)
		}
		c.reps = append(c.reps, r)
	}
	return c
}

func (c *cluster) replicaAt(addr string) int {
	for i, a := range memberAddrs {
		if a == addr {
			return i
		}
	}
	return -1
}

// op is client cl's request number req's operation.
func op(cl, req uint64) string { return fmt.Sprintf("SET c%d r%d", cl, req) }

func clientAddr(cl uint64) ipv4port.IPv4Port {
	var a ipv4port.IPv4Port
	if err := a.FromHostPort(fmt.Sprintf("127.0.0.1:%d", 9000+cl)); err != nil {
		panic(err)
	}
	return a
}

func entry(cl, req uint64) log.Log { return log.Log{Data: op(cl, req), ClientID: cl, RequestID: req} }

// drain runs replica i until its submission queue is empty (internal events included).
func (c *cluster) drain(i int) {
	for !c.reps[i].internal.sq.Empty() {
		c.reps[i].Run()
	}
}

// submit gives replica i the event ev from src and runs it.
func (c *cluster) submit(i int, src ipv4port.IPv4Port, typ events.EventType, data any) {
	c.reps[i].Submit(events.NetworkEvent{Src: src, Event: &events.Event{Type: typ, Data: data}})
	c.drain(i)
}

// request is client cl's request req (sent or resent) arriving at replica i.
func (c *cluster) request(i int, cl, req uint64) {
	c.submit(i, clientAddr(cl), events.EventRequest, events.Request{ID: req, ClientID: cl, Op: op(cl, req)})
}

// timeout lets replica i's view-change timer expire: it proposes a view change (view + 1).
func (c *cluster) timeout(i int) {
	c.submit(i, ipv4port.IPv4Port{}, ProposeViewChange, nil)
}

type pred func(m msg) bool

func any_(m msg) bool { return true }

func typ(ts ...events.EventType) pred {
	return func(m msg) bool {
		for _, t := range ts {
			if m.ev.Type == t {
				return true
			}
		}
		return false
	}
}

func from(is ...int) pred {
	return func(m msg) bool {
		for _, i := range is {
			if m.from == i {
				return true
			}
		}
		return false
	}
}

func to(is ...int) pred {
	return func(m msg) bool {
		for _, i := range is {
			if m.to == memberAddrs[i] {
				return true
			}
		}
		return false
	}
}

// among: from and to replicas of the set.
func among(is ...int) pred { return and(from(is...), to(is...)) }

func and(ps ...pred) pred {
	return func(m msg) bool {
		for _, p := range ps {
			if !p(m) {
				return false
			}
		}
		return true
	}
}

func not(p pred) pred { return func(m msg) bool { return !p(m) } }

// deliver delivers, in the order sent, the pending events that match p (also those sent while
// delivering), until none matches; it returns how many it delivered.
func (c *cluster) deliver(p pred) int {
	n := 0
	for {
		k := -1
		for j, m := range c.pending {
			if p(m) {
				k = j
				break
			}
		}
		if k < 0 {
			return n
		}
		m := c.pending[k]
		c.pending = append(c.pending[:k:k], c.pending[k+1:]...)
		i := c.replicaAt(m.to)
		ev := m.ev
		c.reps[i].Submit(events.NetworkEvent{Src: c.addrs[m.from], Event: &ev})
		c.drain(i)
		n++
	}
}

// drop removes the pending events that match p (lost by the network).
func (c *cluster) drop(p pred) int {
	kept := c.pending[:0:0]
	n := 0
	for _, m := range c.pending {
		if p(m) {
			n++
		} else {
			kept = append(kept, m)
		}
	}
	c.pending = kept
	return n
}

// take removes and returns the pending events that match p (held, to be delivered later with
// resubmit).
func (c *cluster) take(p pred) []msg {
	var out []msg
	kept := c.pending[:0:0]
	for _, m := range c.pending {
		if p(m) {
			out = append(out, m)
		} else {
			kept = append(kept, m)
		}
	}
	c.pending = kept
	return out
}

// resubmit puts held events back at the end of the pending events.
func (c *cluster) resubmit(ms ...msg) { c.pending = append(c.pending, ms...) }

// viewChange runs a view change to view v among the replicas in set: each receives a
// STARTVIEWCHANGE for v (from another member of set, as that member's own timer would send),
// then the view-change events among set are delivered. Events to or from replicas outside set
// stay pending.
func (c *cluster) viewChange(v uint64, set ...int) {
	for _, i := range set {
		other := set[0]
		if other == i {
			other = set[1]
		}
		if c.reps[i].state.ViewNumber < v || c.reps[i].state.Status != ReplicaStatusViewChange {
			c.submit(i, c.addrs[other], events.EventStartViewChange, events.StartViewChange{ViewNum: v, ReplicaID: uint64(other)})
		}
	}
	c.deliver(and(among(set...), typ(events.EventStartViewChange, events.EventDoViewChange, events.EventStartView)))
}

// checkAtMostOnce: each replica executes each request (each op is one client's request) at
// most once.
func (c *cluster) checkAtMostOnce(rule string) {
	c.t.Helper()
	for i, ex := range c.executed {
		seen := map[string]int{}
		for k, o := range ex {
			if j, ok := seen[o]; ok {
				c.t.Fatalf("%s: replica %d executed %q twice (op numbers %d and %d); executed: %q", rule, i, o, j+1, k+1, ex)
			}
			seen[o] = k
		}
	}
}

// checkAgreement: the ops replicas executed at each op number agree (each executed sequence is
// a prefix of the others').
func (c *cluster) checkAgreement(rule string) {
	c.t.Helper()
	for i := range c.executed {
		for j := range c.executed {
			a, b := c.executed[i], c.executed[j]
			for k := 0; k < len(a) && k < len(b); k++ {
				if a[k] != b[k] {
					c.t.Fatalf("%s: op %d is %q at replica %d and %q at replica %d; executed: %q and %q", rule, k+1, a[k], i, b[k], j, a, b)
				}
			}
		}
	}
}

// checkLogHasExecuted: replica i's log holds, at each op number, the op executed there by any
// replica.
func (c *cluster) checkLogHasExecuted(rule string, i int) {
	c.t.Helper()
	logs := c.reps[i].state.Logs
	for j, ex := range c.executed {
		for k, o := range ex {
			if k >= logs.Len() {
				c.t.Fatalf("%s: replica %d executed %q at op %d, but replica %d's log (view %d) has only %d ops: %v", rule, j, o, k+1, i, c.reps[i].state.ViewNumber, logs.Len(), logs)
			}
			if logs.OpAt(k+1) != o {
				c.t.Fatalf("%s: replica %d executed %q at op %d, but replica %d's log (view %d) has %q there: %v", rule, j, o, k+1, i, c.reps[i].state.ViewNumber, logs.OpAt(k+1), logs)
			}
		}
	}
}

// mustNotPanic runs f; a panic fails the test with the rule.
func mustNotPanic(t *testing.T, rule string, f func()) {
	t.Helper()
	defer func() {
		if p := recover(); p != nil {
			t.Fatalf("%s: panicked: %v", rule, p)
		}
	}()
	f()
}

// checkReplies: every reply sent to client cl's address answers one of cl's requests: it
// carries cl's id, and the result of the request it names.
func (c *cluster) checkReplies(rule string) {
	c.t.Helper()
	for _, m := range c.replies {
		if m.ev.Type != events.EventReply {
			continue
		}
		r := m.ev.Data.(events.Reply)
		var cl uint64
		fmt.Sscanf(m.to, "127.0.0.1:%d", &cl)
		cl -= 9000
		if r.ClientID != cl || r.Result != "res "+op(r.ClientID, r.ID) {
			c.t.Fatalf("%s: replica %d sent client %d (at %s) the reply %+v, which is not the answer to one of client %d's requests", rule, m.from, cl, m.to, r, cl)
		}
	}
}
