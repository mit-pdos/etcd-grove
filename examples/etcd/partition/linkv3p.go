// Package partition is linkv3 (examples/linkv3, retired) under network partitions: three etcd members started
// in-process as examples/etcd/putget3 starts them, each serving its raft handler on its own peer
// listener and etcd's gRPC API on its own client listener, a client connected to each member,
// a partitioner goroutine that cuts and mends the links between members, and between each client
// and its member, on a schedule Main is given, and linkvtxn's workload (lintest.Run with concurrent clients doing gets, lists, puts,
// deletes, multi-operation transactions and compare-and-sets of a few keys, robustness's KV
// traffic without leases and stale reads, each operation through a member picked at random,
// checked by porcupine against linkvtxn's model of etcd's KV; notes/linkv3p-txn-plan.md). Main
// panics if porcupine finds the history not linearizable; the theorem is that it does not, for
// every schedule (notes/partition-plan.md, notes/client-cut-plan.md).
//
// The partitions are etcd's own: EtcdServer.CutPeer and MendPeer, which etcd's integration tests
// use (tests/framework/integration/cluster.go, InjectPartition/RecoverPartition), pause and
// resume the transport's peer, which then drops every message to and from it. Both directions of
// a link are cut and mended together, as those tests do.
//
// The cuts between a client and its member are etcd's own too: each client reaches its member
// through a copy of etcd's integration tests' bridge (third_party/bridge, the TCP proxy of
// ClusterConfig.UseBridge), whose Blackhole drops every byte both ways until Unblackhole closes
// the proxied connections, and whose DropConnections closes them. A client recovers by itself:
// its calls wait for a connection (clientv3's default WaitForReady), and gRPC re-dials the bridge.
//
// The workload is package linkvtxn's (Gen, Apply, Model), imported, so that their proofs carry
// over unchanged; Apply here picks the member. (Until 2026-10-20 it was package linkv's, Puts and
// Gets only.) The start of a member is putget3's (startMember), on
// linkv3p's own member names, cluster token and ports, plus the member's gRPC server.
package partition

import (
	"context"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/etcd/txnlin"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/third_party/bridge"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler), client addresses (each served by the member's gRPC server) and bridge
// addresses (each the bridge to a member's client address, which its client dials: a plain
// host:port, clientv3.New's premise). Not another example's, so that the examples' tests can run
// at once.
const (
	peerAddr1   = "127.0.0.1:23841"
	peerAddr2   = "127.0.0.1:23842"
	peerAddr3   = "127.0.0.1:23843"
	clientAddr1 = "127.0.0.1:23831"
	clientAddr2 = "127.0.0.1:23832"
	clientAddr3 = "127.0.0.1:23833"
	bridgeAddr1 = "127.0.0.1:23851"
	bridgeAddr2 = "127.0.0.1:23852"
	bridgeAddr3 = "127.0.0.1:23853"
)

// The members' snapshot settings (etcdstart.NewMember): a disk snapshot every SnapCount applied
// entries, raft's log then compacted to SnapCatchUp entries below it, so that a member a cut kept
// behind is caught up, once mended, by a snapshot (MsgSnap) rather than by entries; TestMainRun
// reports how often each happened.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

// Apply runs one operation through a client of clis picked at random (txnlin.Apply).
func Apply(clis []*clientv3.Client, input any) any {
	i := primitive.RandomUint64() % uint64(len(clis))
	return txnlin.Apply(clis[i], input)
}

// Check runs lintest.Run of clients concurrent clients, each running ops operations through the
// clients clis (one per member, each operation's picked at random), and returns porcupine's
// verdict against linkvtxn's model.
func Check(clis []*clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(clis, input) }
	return lintest.Run(txnlin.Model(), apply, txnlin.Gen, lintest.CounterClock(), clients, ops,
		timeout)
}

// config is the cluster's (cluster3.Config): linkv3p's token, member names and addresses, and
// snapshot settings.
func config() cluster3.Config {
	return cluster3.Config{
		Token: "linkv3p", Name1: "linkv3p-1", Name2: "linkv3p-2", Name3: "linkv3p-3",
		Peer1: peerAddr1, Peer2: peerAddr2, Peer3: peerAddr3,
		Client1: clientAddr1, Client2: clientAddr2, Client3: clientAddr3,
		Bridge1: bridgeAddr1, Bridge2: bridgeAddr2, Bridge3: bridgeAddr3,
		SnapCount: SnapCount, SnapCatchUp: SnapCatchUp,
	}
}

// startCluster starts the three members of a new cluster and a bridge to each member's client
// address (cluster3.StartCluster), and three clients, each of every bridge (cluster3.NewClient:
// failover). It returns the members, the bridges and the clients, and false if a step failed (the
// specs allow every step to fail).
func startCluster(lg *zap.Logger) ([]*etcdserver.EtcdServer, []bridge.Bridge, []*clientv3.Client,
	bool) {
	cfg := config()
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		return nil, nil, nil, false
	}
	cli1, err := cluster3.NewClient(cfg, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	cli2, err := cluster3.NewClient(cfg, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	cli3, err := cluster3.NewClient(cfg, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	clis := []*clientv3.Client{cli1, cli2, cli3}
	return srvs, brs, clis, true
}

// Main starts the cluster (startCluster: three members, a bridge to each, three clients each of
// every bridge), starts the partitioner on sched and runs Check; it panics if porcupine finds the
// history illegal. A failed start ends Main without a check.
func Main(clients int, ops int, sched []cluster3.Step) porcupine.CheckResult {
	srvs, brs, clis, ok := startCluster(zap.NewNop())
	if !ok {
		return porcupine.Unknown
	}
	go cluster3.Partitioner(srvs, brs, sched)
	r := Check(clis, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv3p: porcupine found the history not linearizable")
	}
	return r
}

// The watch workload (notes/watch-cut-plan.md, W4): examples/etcd/watch's, over the cluster. The
// writers put random keys under wprefix, each put through a client picked at random; a watch of
// the prefix from revision 1, through the first client, opened before any write and kept across
// cuts (the client re-opens its stream at a reachable member and resumes it); then the check that
// the watch reported exactly the writes (etcdstart.Check, watchkv's check).

// The prefix every writer's key is under, and the one the watch covers.
const wprefix = "wk/"

// MainWatch's results: the check passed, a step of the start failed, or the watch ended before it
// had reported every successful put.
const (
	WatchOk     = 0
	WatchFailed = 1
	WatchEnded  = 2
)

// writer does the puts tried[lo:hi] in order, each through a client of clis picked at random,
// logging in w each that returned no error, with its reply's revision.
func writer(clis []*clientv3.Client, w *etcdstart.Writes, tried []etcdstart.KV, lo int, hi int) {
	for k := lo; k < hi; k++ {
		p := tried[k]
		cli := clis[primitive.RandomUint64()%uint64(len(clis))]
		// each Put in a context with the examples' request timeout, cancelled after the call
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp, err := cli.Put(ctx, p.Key, p.Val)
		cancel()
		if err == nil {
			w.Mu.Lock()
			w.Ok = append(w.Ok, etcdstart.PutRec{Rev: resp.Header.Revision, Key: p.Key, Val: p.Val})
			w.Mu.Unlock()
		}
	}
}

// MainWatch picks the writers' puts, starts the cluster (startCluster), opens a watch of the
// prefix from revision 1 through the first client, starts the partitioner on sched, runs nw
// writers of nops puts each, then reads the watch and checks it against the writes.
func MainWatch(nw int, nops int, sched []cluster3.Step) int {
	// The writers' puts, picked before the members start (the puts attempted).
	tried := etcdstart.GenAll(nw*nops, []string{"wk/k0", "wk/k1", "wk/k2"})

	srvs, brs, clis, ok := startCluster(zap.NewNop())
	if !ok {
		return WatchFailed
	}

	// The watch, from revision 1: every write is after it, whenever a member registers it.
	wctx, cancel := context.WithCancel(context.Background())
	wch := clis[0].Watcher.Watch(wctx, wprefix, clientv3.WithPrefix(), clientv3.WithRev(1),
		clientv3.WithProgressNotify(), clientv3.WithCreatedNotify())

	go cluster3.Partitioner(srvs, brs, sched)
	w := &etcdstart.Writes{}
	var wg sync.WaitGroup
	for i := 0; i < nw; i++ {
		lo := i * nops
		wg.Add(1)
		go func() {
			writer(clis, w, tried, lo, lo+nops)
			wg.Done()
		}()
	}
	wg.Wait()

	// The successful puts, taken out of the log.
	w.Mu.Lock()
	oks := w.Ok
	w.Ok = nil
	w.Mu.Unlock()
	evs, ok2 := etcdstart.Collect(wch, etcdstart.MaxRev(oks))
	cancel()
	if !ok2 {
		return WatchEnded
	}
	etcdstart.Check("linkv3p", "put", evs, tried, oks)
	return WatchOk
}
