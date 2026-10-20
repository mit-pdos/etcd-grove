// Package cachekv is watchkv (examples/watchkv) with the watch read through etcd's cache: one etcd
// member started in-process (as examples/putget starts it), a client connected to it, a cache of
// the prefix over the client (cache.New), a cache watch of the prefix from revision 2 opened before
// any write, writer goroutines putting random keys under the prefix, and watchkv's check that the
// watch reported exactly the writes: Main panics if the check fails; the theorem to prove is that
// it does not (notes/STATUS.md, "cachekv").
//
// The cache's watch starts at revision 2, the first revision after a fresh member's: Cache.Watch
// first waits for the cache to be ready (its first Get, at the member's revision, and its first
// watch response), and a watch from a revision the cache's history no longer holds ends with a
// compaction's cancel response (so does one the cache's history window, HistoryWindowSize,
// outgrew before the watch caught up). The check (check) is watchkv's: the watched events are all
// puts, at strictly increasing revisions, gap-free from revision 2, each the put of a (key, value)
// some writer attempted, and every Put that returned no error is the event at its reply's header
// revision with its key and value. The watch is read after the writers are done, until an event at
// or above the highest revision a successful Put returned; if the channel closes, or a response
// reports an error (a cancel, a compaction), before that, Main returns WatchEnded without a check.
//
// Main calls only what the proofs specify: putget's start (etcdserver.NewServer, Start,
// v3rpc.Server, net.Listen, (*grpc.Server).Serve on a goroutine), clientv3.New, the client's Put,
// cache.New, the cache's Watch, context.WithCancel and WatchResponse.Err. An error from a step of
// the start ends Main with Failed.
package cachekv

import (
	"context"
	"net"
	"sync"

	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/cache/v3"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23851"
	peerAddr   = "127.0.0.1:23861"
)

// The prefix every writer's key is under, and the one the watch covers.
const prefix = "ck/"

// Main's results: the check passed, a step of the start failed, or the watch ended before it had
// reported every successful Put.
const (
	Ok         = 0
	Failed     = 1
	WatchEnded = 2
)

// A kv is a key and a value.
type kv struct {
	key string
	val string
}

// A putRec is a Put that returned no error: its reply's header revision, its key and value.
type putRec struct {
	rev int64
	key string
	val string
}

// An event is a watched event: its revision (its key-value's mod revision), key, value, and
// whether it is a put.
type event struct {
	rev int64
	key string
	val string
	put bool
}

// The writers' log: every Put that returned no error.
type writes struct {
	mu sync.Mutex
	ok []putRec
}

// Gen picks a key under the prefix and a value, from a small set.
func Gen() kv {
	keys := []string{"ck/k0", "ck/k1", "ck/k2"}
	vals := []string{"a", "b", "c", "d"}
	n := primitive.RandomUint64()
	k := keys[n%uint64(len(keys))]
	n = n / uint64(len(keys))
	return kv{key: k, val: vals[n%uint64(len(vals))]}
}

// writer does the Puts tried[lo:hi] through cli, in order, logging in w each that returned no
// error, with its reply's revision.
func writer(cli *clientv3.Client, w *writes, tried []kv, lo int, hi int) {
	ctx := context.Background()
	for k := lo; k < hi; k++ {
		p := tried[k]
		resp, err := cli.Put(ctx, p.key, p.val)
		if err == nil {
			w.mu.Lock()
			w.ok = append(w.ok, putRec{rev: resp.Header.Revision, key: p.key, val: p.val})
			w.mu.Unlock()
		}
	}
}

// genAll picks n Puts (Gen): the writers' Puts, writer i's at [i*nops, (i+1)*nops).
func genAll(n int) []kv {
	var all []kv
	for i := 0; i < n; i++ {
		all = append(all, Gen())
	}
	return all
}

// maxRev is the highest revision of the successful Puts oks (0 if there is none).
func maxRev(oks []putRec) int64 {
	var m int64
	for _, p := range oks {
		if p.rev > m {
			m = p.rev
		}
	}
	return m
}

// collect reads the watch channel wch until an event at revision upTo or above (at once if
// upTo is 0), returning the events read and true; false if the channel closed, or a response
// reported an error, before.
func collect(wch clientv3.WatchChan, upTo int64) ([]event, bool) {
	var evs []event
	var last int64 // the last event's revision
	if upTo == 0 {
		return evs, true
	}
	for wresp := range wch {
		if wresp.Err() != nil {
			return evs, false
		}
		// Gooseable: mvccpb.Event rather than its alias clientv3.Event (the same type): Goose does
		// not resolve a type alias when it selects a field through a pointer.
		var es []*mvccpb.Event = wresp.Events
		for _, e := range es {
			evs = append(evs, event{rev: e.Kv.ModRevision, key: string(e.Kv.Key),
				val: string(e.Kv.Value), put: e.Type == mvccpb.Event_PUT})
			last = e.Kv.ModRevision
		}
		if len(evs) > 0 && last >= upTo {
			return evs, true
		}
	}
	return evs, false
}

// attempted reports whether (key, val) is one of the Puts tried.
func attempted(tried []kv, key string, val string) bool {
	for _, p := range tried {
		if p.key == key && p.val == val {
			return true
		}
	}
	return false
}

// check panics unless the events evs are the writes: all puts, at strictly increasing revisions,
// gap-free from revision 2, each a put some writer attempted (tried), and every successful Put
// (oks) the event at its revision with its key and value.
func check(evs []event, tried []kv, oks []putRec) {
	var prev int64 // the previous event's revision
	for i, e := range evs {
		if !e.put {
			panic("cachekv: a watched event is not a put")
		}
		if i > 0 && e.rev <= prev {
			panic("cachekv: the watched revisions do not increase")
		}
		if e.rev != int64(i)+2 {
			panic("cachekv: the watched revisions are not those from 2 on, without a gap")
		}
		if !attempted(tried, e.key, e.val) {
			panic("cachekv: a watched put no writer attempted")
		}
		prev = e.rev
	}
	for _, p := range oks {
		i := p.rev - 2
		if i < 0 || i >= int64(len(evs)) {
			panic("cachekv: a successful Put's revision was not watched")
		}
		e := evs[i]
		if e.key != p.key || e.val != p.val {
			panic("cachekv: the event at a successful Put's revision is not that Put")
		}
	}
}

// Main starts one member of a new cluster, a cache of the prefix, opens a cache watch of the
// prefix from revision 2, runs nw writers of nops Puts each, then reads the watch and checks it
// against the writes.
func Main(nw int, nops int) int {
	// The writers' Puts, picked before the member starts (the Puts attempted).
	tried := genAll(nw * nops)

	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	cfg := config.ServerConfig{
		Name:                "cachekv",
		DataDir:             "cachekv.etcd",
		InitialPeerURLsMap:  types.URLsMap{"cachekv": peer},
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: clientAddr}},
		InitialClusterToken: "cachekv",
		NewCluster:          true,
		TickMs:              100,
		ElectionTicks:       10,
		// etcd's default snapshot count; the catch-up entries past the theorem's step bound (as
		// examples/putget's: NewServer's run bound, receiptBound <= SnapshotCatchUpEntries + 1)
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate("cachekv", lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return Failed
	}
	s.Start()

	gs := v3rpc.Server(s, nil, nil)
	l, err := net.Listen("tcp", clientAddr)
	if err != nil {
		return Failed
	}
	go gs.Serve(l)

	// One attempt per call (MaxUnaryRetries: 1, as linkv's): a Put is sent at most once, so the
	// server applies it at most once (decision D21i).
	cli, err := clientv3.New(clientv3.Config{
		Endpoints:       []string{clientAddr},
		Logger:          lg,
		MaxUnaryRetries: 1,
	})
	if err != nil {
		return Failed
	}

	// The cache of the prefix, over the client (its options the defaults).
	c, err := cache.New(cli, prefix)
	if err != nil {
		return Failed
	}

	// The cache's watch of the prefix, from revision 2 (the first after a fresh member's): every
	// write is at revision 2 or later. In a context cancelled once the watch has been read.
	wctx, cancel := context.WithCancel(context.Background())
	wch := c.Watch(wctx, prefix, clientv3.WithPrefix(), clientv3.WithRev(2))

	w := &writes{}
	var wg sync.WaitGroup
	for i := 0; i < nw; i++ {
		lo := i * nops
		wg.Add(1)
		go func() {
			writer(cli, w, tried, lo, lo+nops)
			wg.Done()
		}()
	}
	wg.Wait()

	// The successful Puts, taken out of the log (any writer still appending starts a new one).
	w.mu.Lock()
	oks := w.ok
	w.ok = nil
	w.mu.Unlock()
	evs, ok := collect(wch, maxRev(oks))
	cancel()
	if !ok {
		return WatchEnded
	}
	check(evs, tried, oks)
	return Ok
}
