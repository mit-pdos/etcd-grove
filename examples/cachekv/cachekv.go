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
// Main calls only what the proofs specify: the examples' shared start (examples/common's
// StartServer, Serve and NewClient: etcdserver.NewServer, Start, v3rpc.Server, net.Listen,
// (*grpc.Server).Serve on a goroutine, clientv3.New), the client's Put,
// cache.New, the cache's Watch and context.WithCancel. An error from a step of the start ends Main
// with Failed.
package cachekv

import (
	"context"
	"sync"

	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/cache/v3"
	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23873"
	peerAddr   = "127.0.0.1:23883"
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

// collect reads the cache's watch channel wch until an event at revision upTo or above (at once if
// upTo is 0), returning the events read and true; false if the channel closed, or a response
// reported an error, before. The cache's error responses are cancels (cache.go: validateWatch's
// rejection, the compaction's), with Canceled set: their Err() is not nil because of it (the
// cache never sets a response's unexported closeErr), so collect tests the fields.
func collect(wch clientv3.WatchChan, upTo int64) ([]common.Event, bool) {
	var evs []common.Event
	var last int64 // the last event's revision
	if upTo == 0 {
		return evs, true
	}
	for wresp := range wch {
		if wresp.Canceled || wresp.CompactRevision != 0 {
			return evs, false
		}
		// Gooseable: mvccpb.Event rather than its alias clientv3.Event (the same type): Goose does
		// not resolve a type alias when it selects a field through a pointer.
		var es []*mvccpb.Event = wresp.Events
		for _, e := range es {
			evs = append(evs, common.Event{Rev: e.Kv.ModRevision, Key: string(e.Kv.Key),
				Val: string(e.Kv.Value), Put: e.Type == mvccpb.Event_PUT})
			last = e.Kv.ModRevision
		}
		if len(evs) > 0 && last >= upTo {
			return evs, true
		}
	}
	return evs, false
}

// Main starts one member of a new cluster, a cache of the prefix, opens a cache watch of the
// prefix from revision 2, runs nw writers of nops Puts each, then reads the watch and checks it
// against the writes.
func Main(nw int, nops int) int {
	// The writers' Puts, picked before the member starts (the Puts attempted).
	tried := common.GenAll(nw*nops, []string{"ck/k0", "ck/k1", "ck/k2"})

	lg := zap.NewNop()
	s, err := common.StartServer("cachekv", peerAddr, clientAddr, lg)
	if err != nil {
		return Failed
	}
	if err := common.Serve(s, clientAddr); err != nil {
		return Failed
	}

	// etcd's default client configuration (its default retries, as linkv's): the server never
	// answers with a refusal (authentication off, a voter), so a Put is sent at most once and the
	// server applies it at most once (decision D29).
	cli, err := common.NewClient(clientAddr, lg)
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

	w := &common.Writes{}
	var wg sync.WaitGroup
	for i := 0; i < nw; i++ {
		lo := i * nops
		wg.Add(1)
		go func() {
			common.Writer(cli, w, tried, lo, lo+nops)
			wg.Done()
		}()
	}
	wg.Wait()

	// The successful Puts, taken out of the log (any writer still appending starts a new one).
	w.Mu.Lock()
	oks := w.Ok
	w.Ok = nil
	w.Mu.Unlock()
	evs, ok := collect(wch, common.MaxRev(oks))
	cancel()
	if !ok {
		return WatchEnded
	}
	common.Check("cachekv", "Put", evs, tried, oks)
	return Ok
}
