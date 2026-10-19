// Package linkv is the lintest driver instantiated with etcd: one etcd member started in-process
// (as examples/putget does), a client connected to it, and lintest.Run with concurrent clients
// doing Put and Get of a few keys through that client, checked by porcupine against a key-value
// model (Model). Main panics if porcupine finds the history not linearizable; the theorem to
// prove is that it does not (D20: the driver's proof, Proof/github_com/mit_pdos/etcd_grove/
// examples/lintest/, needs each operation logically atomic against the model; the model's proof
// is Proof/github_com/mit_pdos/etcd_grove/examples/linkv/Model.lean).
//
// Apply resolves a prophecy with the call's outcome (D20, part (c)): it creates one before calling
// the client and resolves it with whether the call returned no error after the call returns, so
// that the proof, at the call's linearization point inside the server (the apply of the put, the
// read of the get), knows whether the client will return ok (the output is then the server's) or
// an error. A prophecy has no effect when the program runs (primitive's functions are no-ops).
package linkv

import (
	"context"
	"net"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// An Input is an operation: a Put of Key with Val, or a Get of Key.
type Input struct {
	Put bool
	Key string
	Val string
}

// An Output is an operation's result: Err if the call returned an error; for a Get that did not,
// whether the key was found and its value.
type Output struct {
	Err   bool
	Found bool
	Val   string
}

// A kvEntry is a key and a value.
type kvEntry struct {
	key string
	val string
}

// A kvConfig is a store (at most one entry per key, sorted by key) and the failed puts that may
// still take effect (sorted, as a multiset). Configurations are never modified in place.
type kvConfig struct {
	kv   []kvEntry
	pend []kvEntry
}

// A state is the set of configurations the history may have reached (no duplicates), as etcd's
// robustness model keeps (tests/robustness/model/non_deterministic.go).
type state []kvConfig

func entryLess(a, b kvEntry) bool {
	return a.key < b.key || (a.key == b.key && a.val < b.val)
}

func entriesEqual(a, b []kvEntry) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func configEqual(a, b kvConfig) bool {
	return entriesEqual(a.kv, b.kv) && entriesEqual(a.pend, b.pend)
}

// lookup returns k's value in the store kv.
func lookup(kv []kvEntry, k string) (string, bool) {
	for _, e := range kv {
		if e.key == k {
			return e.val, true
		}
	}
	return "", false
}

// set returns the store kv with k's value v (a new slice).
func set(kv []kvEntry, k, v string) []kvEntry {
	out := make([]kvEntry, 0, len(kv)+1)
	done := false
	for _, e := range kv {
		if !done && k <= e.key {
			out = append(out, kvEntry{key: k, val: v})
			done = true
			if e.key == k {
				continue
			}
		}
		out = append(out, e)
	}
	if !done {
		out = append(out, kvEntry{key: k, val: v})
	}
	return out
}

// insertSorted returns pend with e added (a new slice, sorted).
func insertSorted(pend []kvEntry, e kvEntry) []kvEntry {
	out := make([]kvEntry, 0, len(pend)+1)
	done := false
	for _, x := range pend {
		if !done && !entryLess(x, e) {
			out = append(out, e)
			done = true
		}
		out = append(out, x)
	}
	if !done {
		out = append(out, e)
	}
	return out
}

// removeAt returns pend without its i-th entry (a new slice).
func removeAt(pend []kvEntry, i int) []kvEntry {
	out := make([]kvEntry, 0, len(pend))
	out = append(out, pend[:i]...)
	return append(out, pend[i+1:]...)
}

func addConfig(s state, c kvConfig) state {
	for _, d := range s {
		if configEqual(c, d) {
			return s
		}
	}
	return append(s, c)
}

// closure adds to s every configuration reachable by pending puts taking effect.
func closure(s state) state {
	out := state{}
	work := append([]kvConfig{}, s...)
	for len(work) > 0 {
		c := work[len(work)-1]
		work = work[:len(work)-1]
		n := len(out)
		out = addConfig(out, c)
		if len(out) == n {
			continue
		}
		for i, e := range c.pend {
			work = append(work, kvConfig{kv: set(c.kv, e.key, e.val), pend: removeAt(c.pend, i)})
		}
	}
	return out
}

// step returns the configurations c steps to by (in, out), the model's CStep.
func step(c kvConfig, in Input, out Output) []kvConfig {
	if in.Put {
		if out.Err {
			return []kvConfig{{kv: c.kv, pend: insertSorted(c.pend, kvEntry{key: in.Key, val: in.Val})}}
		}
		if out.Found || out.Val != "" {
			return nil
		}
		return []kvConfig{{kv: set(c.kv, in.Key, in.Val), pend: c.pend}}
	}
	if out.Err {
		return []kvConfig{c}
	}
	v, ok := lookup(c.kv, in.Key)
	if ok != out.Found || (ok && v != out.Val) || (!ok && out.Val != "") {
		return nil
	}
	return []kvConfig{c}
}

// Model is the key-value store's porcupine model: a Put that returned no error took effect, a
// Get that returned no error read the store, a Put that failed may take effect at any later
// time, or never, and a Get that failed constrains nothing.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return state{kvConfig{}} },
		Step: func(st, input, output any) (bool, any) {
			in := input.(Input)
			out := output.(Output)
			next := state{}
			for _, c := range st.(state) {
				for _, d := range step(c, in, out) {
					next = addConfig(next, d)
				}
			}
			next = closure(next)
			return len(next) > 0, next
		},
		Equal: func(a, b any) bool {
			sa := a.(state)
			sb := b.(state)
			if len(sa) != len(sb) {
				return false
			}
			for i := range sa {
				if !configEqual(sa[i], sb[i]) {
					return false
				}
			}
			return true
		},
	}
}

var keys = []string{"k0", "k1", "k2"}
var vals = []string{"a", "b", "c", "d"}

// Gen picks an operation at random: a Put of a random value or a Get, of a random key.
func Gen(id int) any {
	n := primitive.RandomUint64()
	k := keys[n%uint64(len(keys))]
	n = n / uint64(len(keys))
	if n%2 == 0 {
		return Input{Put: true, Key: k, Val: vals[(n/2)%uint64(len(vals))]}
	}
	return Input{Key: k}
}

// Apply runs one operation through the client cli, resolving a prophecy with its outcome.
func Apply(cli *clientv3.Client, input any) any {
	in := input.(Input)
	p := primitive.NewProph()
	ctx := context.Background()
	var out Output
	if in.Put {
		if _, err := cli.Put(ctx, in.Key, in.Val); err != nil {
			out = Output{Err: true}
		}
	} else {
		resp, err := cli.Get(ctx, in.Key)
		if err != nil {
			out = Output{Err: true}
		} else if len(resp.Kvs) > 0 {
			out = Output{Found: true, Val: string(resp.Kvs[0].Value)}
		}
	}
	p.ResolveBool(!out.Err)
	return out
}

// Check runs lintest.Run of clients concurrent clients of cli, each running ops operations, and
// returns porcupine's verdict.
func Check(cli *clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(cli, input) }
	return lintest.Run(Model(), apply, Gen, lintest.CounterClock(), clients, ops, timeout)
}

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme: clientv3.New's premise plainEndpoint). Not putget's, so that the two
// examples' tests can run at once.
const clientAddr = "127.0.0.1:23791"

// Main starts one member of a new cluster (as examples/putget's Main does), connects a client
// and runs Check; it panics if porcupine finds the history illegal. An error from a step before
// Check ends Main without a check (the specs allow every step to fail).
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23801"}}
	cfg := config.ServerConfig{
		Name:                   "linkv",
		DataDir:                "linkv.etcd",
		InitialPeerURLsMap:     types.URLsMap{"linkv": peer},
		PeerURLs:               peer,
		ClientURLs:             types.URLs{{Scheme: "http", Host: clientAddr}},
		InitialClusterToken:    "linkv",
		NewCluster:             true,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: etcdserver.DefaultSnapshotCatchUpEntries,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate("linkv", lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return porcupine.Unknown
	}
	s.Start()

	gs := v3rpc.Server(s, nil, nil)
	l, err := net.Listen("tcp", clientAddr)
	if err != nil {
		return porcupine.Unknown
	}
	go gs.Serve(l)

	cli, err := clientv3.New(clientv3.Config{
		Endpoints: []string{clientAddr},
		Logger:    lg,
	})
	if err != nil {
		return porcupine.Unknown
	}
	r := Check(cli, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv: porcupine found the history not linearizable")
	}
	return r
}
