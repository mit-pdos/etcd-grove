package replica

// A randomized in-process stress test of the protocol's safety properties: 3 replicas (or 5:
// STRESS_N) and
// several go-vsr clients over a simulated network with TCP's guarantees (per directed link,
// events arrive in the order sent, after random delays; a link may break, losing every event in
// flight on it, i.e. a suffix of its stream, and stay down for a while), with replicas cut off
// for a while (forcing view changes) and PREPAREs lost to single backups (forcing state
// transfers). Virtual time; one goroutine. Checked directly on every run:
//   (a) each replica executes each client request (client id, request id) at most once;
//   (b) the replicas' executed sequences are prefixes of one another (agreement);
//   (c) every reply a client accepts carries its client id and its request's id, and the
//       result its request produced.
// Self-contained (no harness_test.go helpers), so that it also runs on the code as released.

import (
	"bytes"
	"fmt"
	"io"
	"log/slog"
	"math/rand"
	"os"
	"strconv"
	"testing"

	"github.com/tangledbytes/go-vsr/pkg/client"
	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
	vsrtime "github.com/tangledbytes/go-vsr/pkg/time"
)

const (
	stNClients  = 4
	stRequests  = 6 // per client
	stSteps     = 30000
	stTick      = vsrtime.MILLISECOND // one step of virtual time
)

// stNReplicas is the number of replicas (STRESS_N: 3, the default, or 5, f = 2) and
// stReplicaAddrs their addresses.
var stNReplicas, stReplicaAddrs = stReplicas()

func stReplicas() (int, []string) {
	n := 3
	if s := os.Getenv("STRESS_N"); s != "" {
		n, _ = strconv.Atoi(s)
	}
	var addrs []string
	for i := 0; i < n; i++ {
		addrs = append(addrs, "127.0.0.1:"+strconv.Itoa(7101+i))
	}
	return n, addrs
}

func stClientAddr(c int) string { return fmt.Sprintf("127.0.0.1:%d", 7200+c) }

// stNode: replicas 0..2, clients 3..
type stInFlight struct {
	at  uint64
	src string
	ev  events.Event
}

type stWorld struct {
	rng   *rand.Rand
	clock *vsrtime.Virtual
	nodes []string // node index -> address
	index map[string]int
	// links[src][dst]: events in flight, in send order (TCP order per connection)
	links  [][][]stInFlight
	downTo [][]uint64 // link down (sends lost) until this time
	inbox  [][]events.NetworkEvent
}

type stNet struct {
	w   *stWorld
	src int
}

func (n *stNet) Send(to ipv4port.IPv4Port, f func(io.Writer) error) error {
	w := n.w
	dst, ok := w.index[to.String()]
	if !ok {
		return fmt.Errorf("no route to %s", to.String())
	}
	now := w.clock.Now()
	if now < w.downTo[n.src][dst] {
		// a broken connection: the send fails (as a refused dial) or is lost on the stream
		if w.rng.Intn(2) == 0 {
			return fmt.Errorf("connection to %s broken", to.String())
		}
		return nil
	}
	var buf bytes.Buffer
	if err := f(&buf); err != nil {
		return err
	}
	var ev events.Event
	if err := ev.FromReader(&buf); err != nil {
		return err
	}
	at := now + uint64(1+w.rng.Intn(8))*stTick
	l := w.links[n.src][dst]
	if len(l) > 0 && l[len(l)-1].at > at {
		at = l[len(l)-1].at
	}
	w.links[n.src][dst] = append(l, stInFlight{at: at, src: w.nodes[n.src], ev: ev})
	return nil
}

func (n *stNet) Recv() (events.NetworkEvent, bool) {
	q := n.w.inbox[n.src]
	if len(q) == 0 {
		return events.NetworkEvent{}, false
	}
	n.w.inbox[n.src] = q[1:]
	return q[0], true
}

// breakLink loses every event in flight from a to b (a suffix of the stream) and keeps the
// link down for d.
func (w *stWorld) breakLink(a, b int, d uint64) {
	w.links[a][b] = nil
	w.downTo[a][b] = w.clock.Now() + d
}

func (w *stWorld) deliverDue() {
	now := w.clock.Now()
	for a := range w.links {
		for b := range w.links[a] {
			l := w.links[a][b]
			k := 0
			for k < len(l) && l[k].at <= now {
				var src ipv4port.IPv4Port
				if err := src.FromHostPort(l[k].src); err != nil {
					panic(err)
				}
				ev := l[k].ev
				w.inbox[b] = append(w.inbox[b], events.NetworkEvent{Src: src, Event: &ev})
				k++
			}
			w.links[a][b] = l[k:]
		}
	}
}

type stResult struct {
	fail     string // "" if every check held
	accepted int    // replies accepted by clients
	views    uint64 // largest view reached
	transfer bool   // a state transfer started
}

func stOp(c, r uint64) string { return fmt.Sprintf("SET c%d r%d", c, r) }

func stRun(seed int64) (res stResult) {
	rng := rand.New(rand.NewSource(seed))
	clock := vsrtime.NewVirtual(stTick)
	n := stNReplicas + stNClients
	w := &stWorld{rng: rng, clock: clock, index: map[string]int{}}
	for i := 0; i < n; i++ {
		a := ""
		if i < stNReplicas {
			a = stReplicaAddrs[i]
		} else {
			a = stClientAddr(i - stNReplicas)
		}
		w.nodes = append(w.nodes, a)
		w.index[a] = i
		w.links = append(w.links, make([][]stInFlight, n))
		w.downTo = append(w.downTo, make([]uint64, n))
		w.inbox = append(w.inbox, nil)
	}
	logger := slog.New(slog.DiscardHandler)
	executed := make([][]string, stNReplicas)
	var reps []*Replica
	for i := 0; i < stNReplicas; i++ {
		i := i
		r, err := New(Config{
			HeartbeatTimeout: 50 * stTick,
			SrvHandler: func(op string) string {
				executed[i] = append(executed[i], op)
				return "res " + op
			},
			Network: &stNet{w: w, src: i},
			Time:    clock,
			ID:      uint64(i),
			Members: stReplicaAddrs,
			Logger:  logger,
		})
		if err != nil {
			panic(err)
		}
		reps = append(reps, r)
	}
	type stClient struct {
		c       *client.Client
		net     *stNet
		id      uint64
		next    uint64 // request number of the request in progress (0: none yet)
		waiting bool
	}
	var cls []*stClient
	for c := 0; c < stNClients; c++ {
		net := &stNet{w: w, src: stNReplicas + c}
		vc, err := client.New(client.Config{ID: uint64(c + 1), Members: stReplicaAddrs, Network: net,
			Time: clock, RequestTimeout: 120 * stTick, Logger: logger})
		if err != nil {
			panic(err)
		}
		cls = append(cls, &stClient{c: vc, net: net, id: uint64(c + 1)})
	}

	defer func() {
		if p := recover(); p != nil {
			res.fail = fmt.Sprintf("panic: %v", p)
		}
	}()

	check := func() string {
		for i, ex := range executed {
			seen := map[string]bool{}
			for _, o := range ex {
				if seen[o] {
					return fmt.Sprintf("(a) replica %d executed %q twice", i, o)
				}
				seen[o] = true
			}
		}
		for i := range executed {
			for j := range executed {
				a, b := executed[i], executed[j]
				for k := 0; k < len(a) && k < len(b); k++ {
					if a[k] != b[k] {
						return fmt.Sprintf("(b) op %d is %q at replica %d and %q at replica %d", k+1, a[k], i, b[k], j)
					}
				}
			}
		}
		return ""
	}

	for step := 0; step < stSteps; step++ {
		clock.Tick()
		now := clock.Now()
		// faults
		switch x := rng.Intn(1000); {
		case x < 3: // a replica is cut off for a while (its links both ways break)
			i := rng.Intn(stNReplicas)
			d := uint64(100+rng.Intn(400)) * stTick
			for j := 0; j < n; j++ {
				if j != i {
					w.breakLink(i, j, d)
					w.breakLink(j, i, d)
				}
			}
		case x < 8: // one link breaks
			a, b := rng.Intn(n), rng.Intn(stNReplicas)
			if a != b {
				w.breakLink(a, b, uint64(rng.Intn(60))*stTick)
			}
		case x < 14: // PREPAREs in flight to one backup are lost (it falls behind)
			b := rng.Intn(stNReplicas)
			for a := 0; a < stNReplicas; a++ {
				kept := w.links[a][b][:0:0]
				dropped := false
				for _, m := range w.links[a][b] {
					if dropped || m.ev.Type == events.EventPrepare {
						dropped = true // a suffix of the stream is lost
						continue
					}
					kept = append(kept, m)
				}
				w.links[a][b] = kept
			}
		}
		_ = now
		w.deliverDue()
		// replicas: each delivered event submitted and run (the event loop), then timers
		for i, r := range reps {
			for {
				ev, ok := (&stNet{w: w, src: i}).Recv()
				if !ok {
					break
				}
				r.Submit(ev)
				r.Run()
			}
			for !r.internal.sq.Empty() {
				r.Run()
			}
			r.Run()
			if s := r.state; s.ViewNumber > res.views {
				res.views = s.ViewNumber
			}
			if r.state.Status == ReplicaStatusStateTransfer {
				res.transfer = true
			}
		}
		// clients
		for _, cl := range cls {
			if !cl.waiting && cl.next < stRequests && rng.Intn(20) == 0 {
				cl.next++
				cl.waiting = true
				cl.c.Request(stOp(cl.id, cl.next))
			}
			for {
				ev, ok := cl.net.Recv()
				if !ok {
					break
				}
				cl.c.Submit(ev)
			}
			cl.c.Run()
			if rep, ok := cl.c.CheckResult(); ok {
				if !cl.waiting || rep.ClientID != cl.id || rep.ID != cl.next || rep.Result != "res "+stOp(cl.id, cl.next) {
					res.fail = fmt.Sprintf("(c) client %d (request %d in progress: %v) accepted the reply %+v", cl.id, cl.next, cl.waiting, rep)
					return res
				}
				cl.waiting = false
				res.accepted++
			}
		}
		if step%100 == 0 {
			if f := check(); f != "" {
				res.fail = f
				return res
			}
		}
	}
	res.fail = check()
	return res
}

// TestStressSafety runs the randomized schedules (STRESS_RUNS, default 100; STRESS_SEED, the
// first seed) and fails on the first run that breaks (a), (b) or (c), or panics.
func TestStressSafety(t *testing.T) {
	runs, seed := 100, int64(1)
	if s := os.Getenv("STRESS_RUNS"); s != "" {
		runs, _ = strconv.Atoi(s)
	}
	if s := os.Getenv("STRESS_SEED"); s != "" {
		seed, _ = strconv.ParseInt(s, 10, 64)
	}
	if testing.Short() {
		runs = 10
	}
	fails := map[string]int{}
	nfail, accepted, viewChanged, transfers := 0, 0, 0, 0
	first := ""
	for k := 0; k < runs; k++ {
		r := stRun(seed + int64(k))
		accepted += r.accepted
		if r.views > 0 {
			viewChanged++
		}
		if r.transfer {
			transfers++
		}
		if r.fail != "" {
			nfail++
			kind := r.fail
			if len(kind) > 3 {
				kind = kind[:3]
			}
			fails[kind]++
			if first == "" {
				first = fmt.Sprintf("seed %d: %s", seed+int64(k), r.fail)
			}
		}
	}
	t.Logf("runs %d, failed %d %v; replies accepted %d (of %d requests); runs with a view change %d, with a state transfer %d",
		runs, nfail, fails, accepted, runs*stNClients*stRequests, viewChanged, transfers)
	if nfail > 0 {
		t.Fatalf("%d of %d runs broke a safety check; first: %s", nfail, runs, first)
	}
}
