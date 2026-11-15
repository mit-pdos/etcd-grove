// Package crashreconf is txnlin's workload (examples/etcd/txnlin: lintest.Run of concurrent
// clients doing gets, lists, puts, deletes and transactions, checked by porcupine against txnlin's
// model of etcd's KV) on an etcd cluster whose members crash individually and whose membership
// changes at random, written as a distributed program (notes/specs-only/crashreconf-test.md): one
// boot function per node, the program the end theorem is about, in Perennial's distributed
// GooseLang (DistLang.lean: each node has its own threads and disk, a node crashes alone and
// reruns its boot function from what its disk keeps; the network and the other nodes go on).
//
//   - NSlots member nodes, MemberNode(i) each: a fixed pool of slots, of which the first NInitial
//     form the initial cluster. A slot hosts a sequence of etcd members (incarnations): it
//     bootstraps (an initial slot) or restarts its member from its data directory (as etcd's main
//     does), or waits until the cluster lists it as added and joins; when its member is removed it
//     stops serving and waits to be added again, as a new member with a fresh data directory.
//   - One client node, ClientNode, which never crashes: txnlin's workload through clients of the
//     cluster's voters, and a goroutine making random membership changes (MemberAddAsLearner, then
//     MemberPromote; MemberRemove), one at a time. It panics if porcupine finds the history not
//     linearizable; the theorem to prove is that it does not.
//
// Every address, name and the initial cluster are the package's constants, so a boot function
// takes only its slot. The real run (crashreconf_test.go, not translated) runs each member node in
// a process of its own and kills them at random.
package crashreconf

import (
	"context"
	"net"
	"net/http"
	"os"
	"sync/atomic"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/storage/wal"

	"github.com/mit-pdos/etcd-grove/examples/etcd/txnlin"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// The cluster: NSlots member slots, the first NInitial of them the initial cluster, with the
// cluster token Token; at least MinVoters voters are kept (and at most NSlots).
const (
	NSlots    = 5
	NInitial  = 3
	MinVoters = 3
	Token     = "crashreconf"
)

// The members' snapshot settings (etcd's --snapshot-count and
// --experimental-snapshot-catchup-entries): a disk snapshot every SnapCount applied entries,
// raft's log then compacted to SnapCatchUp entries below it, so that a joining learner or a
// restarted member is caught up by a snapshot as well as by entries.
const (
	SnapCount   uint64 = 10
	SnapCatchUp uint64 = 5
)

// The client node: NKVClients clients for the workload; a learner not promoted after
// MaxPromoteTries rounds of the reconfiguration goroutine is removed.
const (
	NKVClients      = 3
	MaxPromoteTries = 20
)

// What the reconfiguration goroutine logs after each change that returned no error (the real run
// counts them).
const (
	MsgAdded          = "crashreconf: learner added"
	MsgPromoted       = "crashreconf: learner promoted"
	MsgRemoved        = "crashreconf: voter removed"
	MsgLearnerRemoved = "crashreconf: learner removed"
)

// What a member node logs (the real run counts them in the nodes' logs).
const (
	MsgListenFailed = "crashreconf: listen failed"
	MsgStartFailed  = "crashreconf: NewServer failed"
	MsgStarted      = "crashreconf: member started"
	MsgStopped      = "crashreconf: member stopped"
	MsgRetired      = "crashreconf: member marked removed"
)

// itoa is strconv.Itoa of a non-negative number (examples/mvccrand's).
func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	var b []byte
	for n > 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n /= 10
	}
	return string(b)
}

// peerAddr is slot i's peer address: its members' one peer URL is http://<peerAddr>, served by
// the member's peer handler. Not another example's, so that the examples' tests can run at once.
func peerAddr(i int) string {
	return "127.0.0.1:" + itoa(24301+i)
}

// ClientAddr is slot i's client address, served by its member's gRPC server (a plain host:port,
// clientv3.New's premise).
func ClientAddr(i int) string {
	return "127.0.0.1:" + itoa(24311+i)
}

// peerURL is slot i's peer URL, as the member list reports it.
func peerURL(i int) string {
	return "http://" + peerAddr(i)
}

// peerURLs is slot i's peer URLs (the one URL http://<peerAddr>).
func peerURLs(i int) types.URLs {
	return types.URLs{{Scheme: "http", Host: peerAddr(i)}}
}

// memberName is the name of slot i's k-th member (its incarnation k).
func memberName(i int, k int) string {
	return "s" + itoa(i) + "-" + itoa(k)
}

// dataDir is the data directory of the member name (relative: the node's own directory).
func dataDir(name string) string {
	return name + ".etcd"
}

// markerPath is the file whose existence says that the member name was removed from the cluster.
func markerPath(name string) string {
	return name + ".removed"
}

// initialCluster is the initial cluster: the first incarnation of each initial slot.
func initialCluster() types.URLsMap {
	m := types.URLsMap{}
	for i := 0; i < NInitial; i++ {
		m[memberName(i, 0)] = peerURLs(i)
	}
	return m
}

// clientAddrs is the client addresses of the slots, but slot skip's (-1 for none).
func clientAddrs(skip int) []string {
	eps := make([]string, 0, NSlots)
	for i := 0; i < NSlots; i++ {
		if i != skip {
			eps = append(eps, ClientAddr(i))
		}
	}
	return eps
}

// ---------------------------------------------------------------------------------------------
// The member list

// A mem is a member as the member list reports it: its id, its name (empty until it started), its
// slot (by its peer URL; -1 if it is none of the slots'), and whether it is a learner.
type mem struct {
	id      uint64
	name    string
	slot    int
	learner bool
}

// slotOf is the slot whose peer URL is urls' one URL, or -1.
func slotOf(urls []string) int {
	if len(urls) != 1 {
		return -1
	}
	for i := 0; i < NSlots; i++ {
		if urls[0] == peerURL(i) {
			return i
		}
	}
	return -1
}

// memberList is the cluster's members (a linearizable MemberList through cli, in a context with the
// request timeout), and false if the call failed.
func memberList(cli *clientv3.Client) ([]mem, bool) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := cli.MemberList(ctx)
	cancel()
	if err != nil {
		return nil, false
	}
	out := make([]mem, 0, len(resp.Members))
	for _, m := range resp.Members {
		out = append(out, mem{id: m.ID, name: m.Name, slot: slotOf(m.PeerURLs), learner: m.IsLearner})
	}
	return out, true
}

// hasID reports whether a member of ms has the id id.
func hasID(ms []mem, id uint64) bool {
	for _, m := range ms {
		if m.id == id {
			return true
		}
	}
	return false
}

// ---------------------------------------------------------------------------------------------
// A member node

// serverConfig is the configuration of the member name of slot i (examples/lib/etcdstart's, with
// the strict reconfiguration check and one learner allowed, etcd's defaults): its peer URLs the
// slot's, its one client URL http://<ClientAddr(i)>, the initial cluster cluster, a new cluster or
// not (newCluster), the auto-compactor off, snapshots at SnapCount and SnapCatchUp.
func serverConfig(name string, i int, cluster types.URLsMap, newCluster bool,
	lg *zap.Logger) config.ServerConfig {
	return config.ServerConfig{
		Name:                   name,
		DataDir:                dataDir(name),
		InitialPeerURLsMap:     cluster,
		PeerURLs:               peerURLs(i),
		ClientURLs:             types.URLs{{Scheme: "http", Host: ClientAddr(i)}},
		InitialClusterToken:    Token,
		NewCluster:             newCluster,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          SnapCount,
		SnapshotCatchUpEntries: SnapCatchUp,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		// etcd's defaults (--strict-reconfig-check, --max-learners), which the zero values turn off
		StrictReconfigCheck: true,
		MaxLearners:         1,
		// etcd's default --pre-vote (the user's choice, 2026-11-10; etcdstart's members keep it off)
		PreVote: true,
		// the auto-compactor off (a zero retention), as etcdstart's members
		AutoCompactionMode: "revision",
		Logger:             lg,
		ServerFeatureGate:  features.NewDefaultServerFeatureGate(name, lg),
	}
}

// A running member: its server, its gRPC server and its peer listener (the gRPC server's Stop
// closes the client listener).
type member struct {
	s  *etcdserver.EtcdServer
	gs *grpc.Server
	pl net.Listener
}

// exists reports whether the file path exists (it opens for reading).
func exists(path string) bool {
	f, err := os.OpenFile(path, os.O_RDONLY, 0)
	if err != nil {
		return false
	}
	f.Close()
	return true
}

// markRemoved creates the file path (the marker that a member was removed). Its durability does
// not matter: a lost marker only makes the node restart the removed member, which its peers stop
// again, and write it again.
func markRemoved(path string) {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		return
	}
	f.Sync()
	f.Close()
}

// incarnation is slot i's current incarnation: the first whose member is not marked removed.
func incarnation(i int) int {
	k := 0
	for exists(markerPath(memberName(i, k))) {
		k++
	}
	return k
}

// connect is a client of the other slots' client addresses than i's (-1: every slot's), retried
// until clientv3.New returns one.
func connect(i int, lg *zap.Logger) *clientv3.Client {
	for {
		cli, err := etcdstart.NewClients(clientAddrs(i), lg)
		if err == nil {
			return cli
		}
		time.Sleep(500 * time.Millisecond)
	}
}

// joinCluster is the initial cluster with which the member name of slot i joins, from the member
// list ms, and true, if ms lists an unstarted member with slot i's peer URL: every member's name
// (name for that one; a placeholder for another unstarted one) with its slot's peer URLs, the
// string `etcdctl member add` prints. Otherwise false.
func joinCluster(ms []mem, i int, name string) (types.URLsMap, bool) {
	found := false
	m := types.URLsMap{}
	for _, x := range ms {
		if x.slot < 0 {
			return nil, false
		}
		n := x.name
		if x.slot == i {
			if x.name != "" {
				return nil, false
			}
			found = true
			n = name
		} else if n == "" {
			n = "unstarted-" + itoa(x.slot)
		}
		m[n] = peerURLs(x.slot)
	}
	return m, found
}

// waitAdded waits until the cluster lists slot i as an unstarted member (an add of its peer URL
// took effect), polling the member list through the other slots, and returns the initial cluster
// with which the member name joins (joinCluster).
func waitAdded(i int, name string, lg *zap.Logger) types.URLsMap {
	cli := connect(i, lg)
	for {
		ms, ok := memberList(cli)
		if ok {
			c, found := joinCluster(ms, i, name)
			if found {
				cli.Close()
				return c
			}
		}
		time.Sleep(300 * time.Millisecond)
	}
}

// startMember starts the k-th member of slot i: bootstrapped or restarted (the first member of an
// initial slot: etcd restarts it if its WAL exists, else bootstraps it), restarted (its WAL
// exists), or joining (waitAdded); its listeners opened first, then the server built, etcd's
// peer handler served (etcdhttp.NewPeerHandler, as etcd's embed serves it: a joiner reads the
// cluster from its peers' /members, a follower forwards MemberPromote to the leader's
// /members/promote; RaftHandler alone answers both 404), the server started and its gRPC API
// served (etcdstart.Serve's). It returns false if a step failed, with nothing left running.
func startMember(i int, k int, lg *zap.Logger) (*member, bool) {
	name := memberName(i, k)
	var cluster types.URLsMap
	newCluster := false
	if k == 0 && i < NInitial {
		cluster = initialCluster()
		newCluster = true
	} else if wal.Exist(dataDir(name) + "/member/wal") {
		// a restart: etcd ignores the initial cluster
		cluster = types.URLsMap{name: peerURLs(i)}
	} else {
		cluster = waitAdded(i, name, lg)
	}
	pl, err := net.Listen("tcp", peerAddr(i))
	if err != nil {
		lg.Warn(MsgListenFailed)
		return nil, false
	}
	cl, err := net.Listen("tcp", ClientAddr(i))
	if err != nil {
		lg.Warn(MsgListenFailed)
		pl.Close()
		return nil, false
	}
	s, err := etcdserver.NewServer(serverConfig(name, i, cluster, newCluster, lg))
	if err != nil {
		lg.Warn(MsgStartFailed)
		pl.Close()
		cl.Close()
		return nil, false
	}
	go http.Serve(pl, etcdhttp.NewPeerHandler(lg, s))
	s.Start()
	// the clients' keepalive pings allowed every 5s, as etcd's embed does (etcdstart.Serve)
	gs := v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
		MinTime: 5 * time.Second,
	}))
	go gs.Serve(cl)
	lg.Info(MsgStarted)
	return &member{s: s, gs: gs, pl: pl}, true
}

// removed reports whether the cluster no longer lists the member id (one member list through the
// slots other than i; false if it failed).
func removed(i int, id uint64, lg *zap.Logger) bool {
	cli := connect(i, lg)
	ms, ok := memberList(cli)
	cli.Close()
	return ok && !hasID(ms, id)
}

// runIncarnation runs slot i's k-th member until its server stops (etcd stops a member that
// applies its own removal, or whose peers answer it was removed), then closes its listeners and,
// if the cluster no longer lists it, marks it removed.
func runIncarnation(i int, k int, lg *zap.Logger) {
	m, ok := startMember(i, k, lg)
	if !ok {
		time.Sleep(500 * time.Millisecond)
		return
	}
	<-m.s.StopNotify()
	lg.Info(MsgStopped)
	m.gs.Stop()
	m.pl.Close()
	if removed(i, uint64(m.s.MemberID()), lg) {
		markRemoved(markerPath(memberName(i, k)))
		lg.Info(MsgRetired)
	}
}

// RunMember is MemberNode with the logger lg (the member's and its clients').
func RunMember(i int, lg *zap.Logger) {
	for {
		runIncarnation(i, incarnation(i), lg)
	}
}

// MemberNode is slot i's boot program, run at the node's start and after every crash, in the
// node's own directory: it runs the slot's current member, and the next one once that is removed,
// forever.
func MemberNode(i int) {
	RunMember(i, zap.NewNop())
}

// ---------------------------------------------------------------------------------------------
// The client node

// Apply runs one operation through a client of clis picked at random (txnlin.Apply).
func Apply(clis []*clientv3.Client, input any) any {
	j := primitive.RandomUint64() % uint64(len(clis))
	return txnlin.Apply(clis[j], input)
}

// Connect returns NKVClients clients for the workload and one for the membership changes, each of
// every slot's client address (etcdstart.NewClients: etcd's default retries), and false if
// clientv3.New failed.
func Connect() ([]*clientv3.Client, *clientv3.Client, bool) {
	kvs := make([]*clientv3.Client, 0, NKVClients)
	for j := 0; j < NKVClients; j++ {
		c, err := etcdstart.NewClients(clientAddrs(-1), zap.NewNop())
		if err != nil {
			return nil, nil, false
		}
		kvs = append(kvs, c)
	}
	admin, err := etcdstart.NewClients(clientAddrs(-1), zap.NewNop())
	if err != nil {
		return nil, nil, false
	}
	return kvs, admin, true
}

// WaitCluster waits until the cluster answers a member list through admin.
func WaitCluster(admin *clientv3.Client) {
	for {
		_, ok := memberList(admin)
		if ok {
			return
		}
		time.Sleep(200 * time.Millisecond)
	}
}

// voterAddrs is the client addresses of the started voters of ms.
func voterAddrs(ms []mem) []string {
	eps := make([]string, 0, len(ms))
	for _, m := range ms {
		if !m.learner && m.name != "" && m.slot >= 0 {
			eps = append(eps, ClientAddr(m.slot))
		}
	}
	return eps
}

func sameStrings(a []string, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for j := range a {
		if a[j] != b[j] {
			return false
		}
	}
	return true
}

// learnerOf is the index in ms of a learner, or -1.
func learnerOf(ms []mem) int {
	for j, m := range ms {
		if m.learner {
			return j
		}
	}
	return -1
}

// freeSlot is a slot picked at random among those no member of ms has, or -1.
func freeSlot(ms []mem) int {
	free := make([]int, 0, NSlots)
	for i := 0; i < NSlots; i++ {
		used := false
		for _, m := range ms {
			if m.slot == i {
				used = true
			}
		}
		if !used {
			free = append(free, i)
		}
	}
	if len(free) == 0 {
		return -1
	}
	return free[primitive.RandomUint64()%uint64(len(free))]
}

// addLearner adds slot i's peer URL as a learner (MemberAddAsLearner), reporting whether the call
// returned no error.
func addLearner(admin *clientv3.Client, i int) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := admin.MemberAddAsLearner(ctx, []string{peerURL(i)})
	cancel()
	return err == nil
}

// promote promotes the learner id (MemberPromote), reporting whether the call returned no error.
func promote(admin *clientv3.Client, id uint64) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := admin.MemberPromote(ctx, id)
	cancel()
	return err == nil
}

// remove removes the member id (MemberRemove), reporting whether the call returned no error.
func remove(admin *clientv3.Client, id uint64) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := admin.MemberRemove(ctx, id)
	cancel()
	return err == nil
}

// pause is the time between two rounds of Reconfigure: 200 to 700ms, at random.
func pause() time.Duration {
	return time.Duration(200+primitive.RandomUint64()%500) * time.Millisecond
}

// Reconfigure changes the cluster's membership at random through admin until done is set, one
// change per round: it reads the member list, points the clients kvs and admin at the started
// voters, then, if a learner exists, promotes it (removing it instead after MaxPromoteTries failed
// rounds), else adds a free slot as a learner (below NSlots voters) or removes a random voter
// (above MinVoters), at random. An error does nothing: the next round reads the list again
// (ErrUnhealthy, ErrLearnerNotReady, ErrMemberNotLearner, ErrIDNotFound, ErrPeerURLExist after
// an add that timed out and took effect, a timeout). Each change that returned no error is
// logged to lg.
func Reconfigure(admin *clientv3.Client, kvs []*clientv3.Client, done *atomic.Bool, lg *zap.Logger) {
	tries := 0
	var eps []string
	for !done.Load() {
		time.Sleep(pause())
		ms, ok := memberList(admin)
		if !ok {
			continue
		}
		if veps := voterAddrs(ms); len(veps) > 0 && !sameStrings(veps, eps) {
			eps = veps
			for _, c := range kvs {
				c.SetEndpoints(eps...)
			}
			admin.SetEndpoints(eps...)
		}
		l := learnerOf(ms)
		if l >= 0 {
			if promote(admin, ms[l].id) {
				lg.Info(MsgPromoted)
				tries = 0
			} else {
				tries++
				if tries >= MaxPromoteTries {
					if remove(admin, ms[l].id) {
						lg.Info(MsgLearnerRemoved)
					}
					tries = 0
				}
			}
			continue
		}
		tries = 0
		free := freeSlot(ms)
		coin := primitive.RandomUint64() % 2
		if len(ms) < NSlots && free >= 0 && (len(ms) <= MinVoters || coin == 0) {
			if addLearner(admin, free) {
				lg.Info(MsgAdded)
			}
		} else if len(ms) > MinVoters {
			v := ms[primitive.RandomUint64()%uint64(len(ms))]
			if remove(admin, v.id) {
				lg.Info(MsgRemoved)
			}
		}
	}
}

// RunClient is ClientNode with the logger lg (Reconfigure's) and porcupine's timeout timeout (0:
// none): it connects (Connect), waits for the cluster (WaitCluster), starts Reconfigure, runs
// lintest.Run of clients concurrent clients of ops operations each of txnlin's workload, each
// through a client picked at random (Apply), then stops Reconfigure; it panics if porcupine finds
// the history illegal. A failed connect ends it without a check.
func RunClient(clients int, ops int, timeout time.Duration, lg *zap.Logger) porcupine.CheckResult {
	kvs, admin, ok := Connect()
	if !ok {
		return porcupine.Unknown
	}
	WaitCluster(admin)
	done := new(atomic.Bool)
	go Reconfigure(admin, kvs, done, lg)
	apply := func(input any) any { return Apply(kvs, input) }
	r := lintest.Run(txnlin.Model(), apply, txnlin.Gen, lintest.CounterClock(), clients, ops, timeout)
	done.Store(true)
	if r == porcupine.Illegal {
		panic("crashreconf: porcupine found the history not linearizable")
	}
	return r
}

// ClientNode is the client node's program (it never crashes): RunClient with no logging and no
// timeout.
func ClientNode(clients int, ops int) porcupine.CheckResult {
	return RunClient(clients, ops, 0, zap.NewNop())
}
