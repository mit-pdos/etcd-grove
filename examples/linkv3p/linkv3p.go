// Package linkv3p is linkv3 (examples/linkv3) under network partitions: three etcd members started
// in-process as examples/putget3 starts them, each serving its raft handler on its own peer
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
package linkv3p

import (
	"context"
	"net"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"

	"github.com/mit-pdos/etcd-grove/examples/common"
	"github.com/mit-pdos/etcd-grove/examples/linkvtxn"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
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

// The kinds of a schedule's step.
const (
	// cut the link between members A and B, both directions (CutPeer)
	PeerCut = 0
	// mend it (MendPeer)
	PeerMend = 1
	// cut member A's client off it: every byte between them dropped (the bridge's Blackhole)
	ClientBlackhole = 2
	// end that: the bridge's connections closed, new ones forwarded (Unblackhole)
	ClientUnblackhole = 3
	// close the connections between member A and its client (the bridge's DropConnections)
	ClientDrop = 4
)

// A Step of a partition schedule: after Delay, its Kind's action on members A and B (indices into
// Main's members, 0 to 2): a peer step cuts or mends the link between A and B in both directions;
// a client step acts on the link between member A and its client (B unused). A step whose
// indices are out of range (or equal, for a peer step), or whose kind is none of the above, does
// nothing.
type Step struct {
	Delay time.Duration
	Kind  int
	A     int
	B     int
}

// startMember starts member name of the new cluster cluster, whose peer URLs are peer (the one
// URL http://peerAddr): the server and its raft handler served on a listener at peerAddr (the
// examples' shared NewMember, with linkv3p's cluster token), the server started, and its gRPC
// server served on a listener at client.
func startMember(name string, peer types.URLs, peerAddr string, client string,
	cluster types.URLsMap, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	// the server (configured as putget3's, with linkv3p's cluster token) and its raft handler
	s, err := common.NewMember(name, peer, peerAddr, client, cluster, "linkv3p", lg)
	if err != nil {
		return nil, err
	}
	// the member's client address, before the server starts (an error leaves nothing running)
	cl, err := net.Listen("tcp", client)
	if err != nil {
		return nil, err
	}
	s.Start()
	// the clients' keepalive pings allowed every 5s, as etcd's embed does with its default
	// GRPCKeepAliveMinTime (grpc's own default refuses a ping more often than every 5 minutes)
	gs := v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
		MinTime: 5 * time.Second,
	}))
	go gs.Serve(cl)
	return s, nil
}

// startBridge starts a bridge at addr to the member's client address client: the listener, then
// the bridge's accept loop (bridge.New).
func startBridge(addr string, client string) (bridge.Bridge, error) {
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, err
	}
	return bridge.New(client, l), nil
}

// peerStep applies a peer step to the members srvs: cuts or mends the link between members a and
// b in both directions (etcd's CutPeer/MendPeer, as its integration tests'
// InjectPartition/RecoverPartition).
func peerStep(srvs []*etcdserver.EtcdServer, kind int, a int, b int) {
	if a < 0 || a >= len(srvs) || b < 0 || b >= len(srvs) || a == b {
		return
	}
	sa := srvs[a]
	sb := srvs[b]
	if kind == PeerCut {
		sa.CutPeer(sb.MemberID())
		sb.CutPeer(sa.MemberID())
	} else {
		sa.MendPeer(sb.MemberID())
		sb.MendPeer(sa.MemberID())
	}
}

// clientStep applies a client step to member a's bridge (brs[a]), as etcd's integration tests
// do (Member.Bridge().Blackhole(), ...); holed[a] says whether that bridge is blackholed. A
// blackhole of a blackholed bridge does nothing: the bridge's Blackhole closes its channel
// unguarded, so a second one would panic (issues/etcd-bridge-blackhole-twice-panic.md).
func clientStep(brs []bridge.Bridge, holed []bool, kind int, a int) {
	if a < 0 || a >= len(brs) {
		return
	}
	br := brs[a]
	if kind == ClientBlackhole {
		if !holed[a] {
			br.Blackhole()
			holed[a] = true
		}
	} else if kind == ClientUnblackhole {
		br.Unblackhole()
		holed[a] = false
	} else {
		br.DropConnections()
	}
}

// partitioner applies the schedule sched to the members srvs and their bridges brs: each step,
// after its delay.
func partitioner(srvs []*etcdserver.EtcdServer, brs []bridge.Bridge, sched []Step) {
	holed := make([]bool, len(brs))
	for _, st := range sched {
		time.Sleep(st.Delay)
		if st.Kind == PeerCut || st.Kind == PeerMend {
			peerStep(srvs, st.Kind, st.A, st.B)
		} else if st.Kind == ClientBlackhole || st.Kind == ClientUnblackhole || st.Kind == ClientDrop {
			clientStep(brs, holed, st.Kind, st.A)
		}
	}
}

// Apply runs one operation through a client of clis picked at random (linkvtxn.Apply).
func Apply(clis []*clientv3.Client, input any) any {
	i := primitive.RandomUint64() % uint64(len(clis))
	return linkvtxn.Apply(clis[i], input)
}

// Check runs lintest.Run of clients concurrent clients, each running ops operations through the
// clients clis (one per member, each operation's picked at random), and returns porcupine's
// verdict against linkvtxn's model.
func Check(clis []*clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(clis, input) }
	return lintest.Run(linkvtxn.Model(), apply, linkvtxn.Gen, lintest.CounterClock(), clients, ops,
		timeout)
}

// newClient connects a client with the default retries to the members (through their bridges)
// at eps, each attempt to one of them: a read that fails with Unavailable is retried, on the next
// member; a write is retried only after a refusal (a learner's, an authentication error), which
// these members never send, so it is sent at most once (notes/read-retry-plan.md). Keepalive
// closes a connection that stops answering (notes/keepalive-plan.md).
func newClient(eps []string, lg *zap.Logger) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints: eps,
		Logger:    lg,
		// keepalive pings every 10s (grpc's floor) while calls are in flight; a ping not answered
		// within 2s closes the connection, so a silently cut member's calls fail and the balancer
		// moves on (production values are larger: Kubernetes' API server uses 30s and 10s)
		DialKeepAliveTime:    10 * time.Second,
		DialKeepAliveTimeout: 2 * time.Second,
	})
}

// startCluster starts the three members of a new cluster, a bridge to each member's client
// address, and three clients, each of every bridge (failover). It returns the members, the
// bridges and the clients, and false if a step failed (the specs allow every step to fail).
func startCluster(lg *zap.Logger) ([]*etcdserver.EtcdServer, []bridge.Bridge, []*clientv3.Client,
	bool) {
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"linkv3p-1": peer1, "linkv3p-2": peer2, "linkv3p-3": peer3}

	s1, err := startMember("linkv3p-1", peer1, peerAddr1, clientAddr1, cluster, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	s2, err := startMember("linkv3p-2", peer2, peerAddr2, clientAddr2, cluster, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	s3, err := startMember("linkv3p-3", peer3, peerAddr3, clientAddr3, cluster, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	srvs := []*etcdserver.EtcdServer{s1, s2, s3}

	br1, err := startBridge(bridgeAddr1, clientAddr1)
	if err != nil {
		return nil, nil, nil, false
	}
	br2, err := startBridge(bridgeAddr2, clientAddr2)
	if err != nil {
		return nil, nil, nil, false
	}
	br3, err := startBridge(bridgeAddr3, clientAddr3)
	if err != nil {
		return nil, nil, nil, false
	}
	brs := []bridge.Bridge{br1, br2, br3}

	// every client has every member's bridge: an attempt goes to one of them (failover)
	eps := []string{bridgeAddr1, bridgeAddr2, bridgeAddr3}
	cli1, err := newClient(eps, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	cli2, err := newClient(eps, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	cli3, err := newClient(eps, lg)
	if err != nil {
		return nil, nil, nil, false
	}
	clis := []*clientv3.Client{cli1, cli2, cli3}
	return srvs, brs, clis, true
}

// Main starts the cluster (startCluster: three members, a bridge to each, three clients each of
// every bridge), starts the partitioner on sched and runs Check; it panics if porcupine finds the
// history illegal. A failed start ends Main without a check.
func Main(clients int, ops int, sched []Step) porcupine.CheckResult {
	srvs, brs, clis, ok := startCluster(zap.NewNop())
	if !ok {
		return porcupine.Unknown
	}
	go partitioner(srvs, brs, sched)
	r := Check(clis, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkv3p: porcupine found the history not linearizable")
	}
	return r
}

// The watch workload (notes/watch-cut-plan.md, W4): examples/watchkv's, over the cluster. The
// writers put random keys under wprefix, each put through a client picked at random; a watch of
// the prefix from revision 1, through the first client, opened before any write and kept across
// cuts (the client re-opens its stream at a reachable member and resumes it); then the check that
// the watch reported exactly the writes (checkWatch, watchkv's check).

// The prefix every writer's key is under, and the one the watch covers.
const wprefix = "wk/"

// MainWatch's results: the check passed, a step of the start failed, or the watch ended before it
// had reported every successful put.
const (
	WatchOk     = 0
	WatchFailed = 1
	WatchEnded  = 2
)

// A kv is a key and a value.
type kv struct {
	key string
	val string
}

// A putRec is a put that returned no error: its reply's header revision, its key and value.
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

// The writers' log: every put that returned no error.
type writes struct {
	mu sync.Mutex
	ok []putRec
}

// genPut picks a key under the prefix and a value, from a small set.
func genPut() kv {
	keys := []string{"wk/k0", "wk/k1", "wk/k2"}
	vals := []string{"a", "b", "c", "d"}
	n := primitive.RandomUint64()
	k := keys[n%uint64(len(keys))]
	n = n / uint64(len(keys))
	return kv{key: k, val: vals[n%uint64(len(vals))]}
}

// genAll picks n puts (genPut): the writers' puts, writer i's at [i*nops, (i+1)*nops).
func genAll(n int) []kv {
	var all []kv
	for i := 0; i < n; i++ {
		all = append(all, genPut())
	}
	return all
}

// writer does the puts tried[lo:hi] in order, each through a client of clis picked at random,
// logging in w each that returned no error, with its reply's revision.
func writer(clis []*clientv3.Client, w *writes, tried []kv, lo int, hi int) {
	ctx := context.Background()
	for k := lo; k < hi; k++ {
		p := tried[k]
		cli := clis[primitive.RandomUint64()%uint64(len(clis))]
		resp, err := cli.Put(ctx, p.key, p.val)
		if err == nil {
			w.mu.Lock()
			w.ok = append(w.ok, putRec{rev: resp.Header.Revision, key: p.key, val: p.val})
			w.mu.Unlock()
		}
	}
}

// maxRev is the highest revision of the successful puts oks (0 if there is none).
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
		// Gooseable: mvccpb.Event rather than its alias clientv3.Event (the same type)
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

// attempted reports whether (key, val) is one of the puts tried.
func attempted(tried []kv, key string, val string) bool {
	for _, p := range tried {
		if p.key == key && p.val == val {
			return true
		}
	}
	return false
}

// checkWatch panics unless the events evs are the writes: all puts, at strictly increasing
// revisions, gap-free from revision 2, each a put some writer attempted (tried), and every
// successful put (oks) the event at its revision with its key and value.
func checkWatch(evs []event, tried []kv, oks []putRec) {
	var prev int64 // the previous event's revision
	for i, e := range evs {
		if !e.put {
			panic("linkv3p: a watched event is not a put")
		}
		if i > 0 && e.rev <= prev {
			panic("linkv3p: the watched revisions do not increase")
		}
		if e.rev != int64(i)+2 {
			panic("linkv3p: the watched revisions are not those from 2 on, without a gap")
		}
		if !attempted(tried, e.key, e.val) {
			panic("linkv3p: a watched put no writer attempted")
		}
		prev = e.rev
	}
	for _, p := range oks {
		i := p.rev - 2
		if i < 0 || i >= int64(len(evs)) {
			panic("linkv3p: a successful put's revision was not watched")
		}
		e := evs[i]
		if e.key != p.key || e.val != p.val {
			panic("linkv3p: the event at a successful put's revision is not that put")
		}
	}
}

// MainWatch picks the writers' puts, starts the cluster (startCluster), opens a watch of the
// prefix from revision 1 through the first client, starts the partitioner on sched, runs nw
// writers of nops puts each, then reads the watch and checks it against the writes.
func MainWatch(nw int, nops int, sched []Step) int {
	// The writers' puts, picked before the members start (the puts attempted).
	tried := genAll(nw * nops)

	srvs, brs, clis, ok := startCluster(zap.NewNop())
	if !ok {
		return WatchFailed
	}

	// The watch, from revision 1: every write is after it, whenever a member registers it.
	wctx, cancel := context.WithCancel(context.Background())
	wch := clis[0].Watcher.Watch(wctx, wprefix, clientv3.WithPrefix(), clientv3.WithRev(1),
		clientv3.WithProgressNotify(), clientv3.WithCreatedNotify())

	go partitioner(srvs, brs, sched)
	w := &writes{}
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
	w.mu.Lock()
	oks := w.ok
	w.ok = nil
	w.mu.Unlock()
	evs, ok2 := collect(wch, maxRev(oks))
	cancel()
	if !ok2 {
		return WatchEnded
	}
	checkWatch(evs, tried, oks)
	return WatchOk
}
