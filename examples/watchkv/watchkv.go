// Package watchkv is the watch example of etcd's server and client: one etcd member started
// in-process (as examples/putget starts it), a client connected to it, a prefix watch from revision
// 1 opened before any write, writer goroutines putting random keys under the prefix, and a check
// that the watch reported exactly the writes: Main panics if the check fails; the theorem to prove
// is that it does not (notes/STATUS.md, "watchkv").
//
// The check (check): the watched events are all puts, at strictly increasing revisions, gap-free
// from revision 2 (a fresh member is at revision 1, and every revision after it is one writer's
// Put of one key: one event per revision), each the put of a (key, value) some writer attempted (a
// Put that returned an error may still have been applied; the writers' Puts are picked before the
// member starts, so the Puts attempted are known then), and every Put that returned no error
// is the event at its reply's header revision with its key and value. The watch is read after the
// writers are done, until an event at or above the highest revision a successful Put returned;
// if the watch channel closes, or a response reports an error (a cancel, a compaction, the
// client's close), before that, Main returns WatchEnded without a check.
//
// Main calls only what the proofs specify: the examples' shared start (examples/common's
// StartServer, Serve and NewClient: etcdserver.NewServer, Start, v3rpc.Server, net.Listen,
// (*grpc.Server).Serve on a goroutine, clientv3.New), the client's Put and Watch, context.WithCancel and WatchResponse.Err. An error from a step of the start ends Main
// with Failed.
package watchkv

import (
	"context"
	"sync"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23831"
	peerAddr   = "127.0.0.1:23841"
)

// The prefix every writer's key is under, and the one the watch covers.
const prefix = "wk/"

// Main's results: the check passed, a step of the start failed, or the watch ended before it had
// reported every successful Put.
const (
	Ok         = 0
	Failed     = 1
	WatchEnded = 2
)

// Main starts one member of a new cluster, opens a watch of the prefix from revision 1, runs nw
// writers of nops Puts each, then reads the watch and checks it against the writes.
func Main(nw int, nops int) int {
	// The writers' Puts, picked before the member starts (the Puts attempted).
	tried := common.GenAll(nw*nops, []string{"wk/k0", "wk/k1", "wk/k2"})

	lg := zap.NewNop()
	s, err := common.StartServer("watchkv", peerAddr, clientAddr, lg)
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

	// The watch, from revision 1: every write is after it, whenever the server registers it.
	// Through the embedded Watcher field (the call cli.Watch promotes), in a context cancelled once
	// the watch has been read.
	wctx, cancel := context.WithCancel(context.Background())
	wch := cli.Watcher.Watch(wctx, prefix, clientv3.WithPrefix(), clientv3.WithRev(1),
		clientv3.WithProgressNotify(), clientv3.WithCreatedNotify())

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
	evs, ok := common.Collect(wch, common.MaxRev(oks))
	cancel()
	if !ok {
		return WatchEnded
	}
	common.Check("watchkv", "Put", evs, tried, oks)
	return Ok
}
