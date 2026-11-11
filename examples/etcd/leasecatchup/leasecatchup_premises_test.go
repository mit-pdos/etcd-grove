package leasecatchup

// The Test phase of lease-mono3 (notes/lease-mono3-plan.md, "Test (2026-11-06)"): Go tests that the
// premises and the claim of etcd_leasecatchup_safe hold of the real code in a real run, and are not
// vacuous. Each test runs Main's steps (scenario, run's steps with observations in between) on a
// cluster of its own addresses (run's are TestMainRun's, and run never stops its members):
//
//   - TestLeasePeersOk: leasePeersOk (LeaseRead.lean): every peer URL answers a POST to
//     /leases/internal (and to /leases, the other path etcd's lease handler serves) not with 200
//     (404), while it does serve the member's raft handler;
//   - TestLeasesNoExpiry: lease.leasesNoExpiry (LessorBackend.lean) at TTL 3600: no lease of any
//     lessor expires or is revoked during the run;
//   - TestCatchUpClaim: run.spec's claim, member 3's own grant listed after its restore, and that
//     the case is not vacuous (member 3's lessor recovered from a snapshot, after the grant);
//   - TestCatchUpMutant: the same run with member 3's lessor dropping, on Recover, the leases it
//     held: the check fails (member 3 lists the last filler but not its own grant);
//   - TestHoldTokenPerMember: cluster3.StartMember's go holdToken(): one goroutine per member.

import (
	"bytes"
	"context"
	"net"
	"net/http"
	"reflect"
	"runtime"
	"strconv"
	"strings"
	"testing"
	"time"
	"unsafe"

	"github.com/prometheus/client_golang/prometheus"
	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/keepalive"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"
	"go.etcd.io/etcd/server/v3/lease/leasepb"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// configAt is config() at the addresses 127.0.0.1:base+11..13 (peer), +21..23 (client),
// +31..33 (bridge), with its own token and names.
func configAt(base int, token string) cluster3.Config {
	a := func(off int) string { return net.JoinHostPort("127.0.0.1", strconv.Itoa(base+off)) }
	cfg := config()
	cfg.Token, cfg.Name1, cfg.Name2, cfg.Name3 = token, token+"-1", token+"-2", token+"-3"
	cfg.Peer1, cfg.Peer2, cfg.Peer3 = a(11), a(12), a(13)
	cfg.Client1, cfg.Client2, cfg.Client3 = a(21), a(22), a(23)
	cfg.Bridge1, cfg.Bridge2, cfg.Bridge3 = a(31), a(32), a(33)
	return cfg
}

// lessorField is the address of EtcdServer's unexported lessor field (a test-only abstraction
// function, as examples/etcd/leasesnap's lessorOf).
func lessorField(s *etcdserver.EtcdServer) *lease.Lessor {
	f := reflect.ValueOf(s).Elem().FieldByName("lessor")
	return (*lease.Lessor)(unsafe.Pointer(f.UnsafeAddr()))
}

func lessorOf(s *etcdserver.EtcdServer) lease.Lessor { return *lessorField(s) }

// lessorBackend is the backend a lessor reads and writes (its unexported field b), which
// lessor.Recover replaces by the snapshot's: a change of it says Recover ran on that lessor.
func lessorBackend(le lease.Lessor) backend.Backend {
	if d, ok := le.(*dropLessor); ok {
		le = d.Lessor
	}
	f := reflect.ValueOf(le).Elem().FieldByName("b")
	return *(*backend.Backend)(unsafe.Pointer(f.UnsafeAddr()))
}

// leaseCounter is the process's etcd_debugging_lease_<name>_total counter (lease/metrics.go;
// one counter for every lessor of the process).
func leaseCounter(t *testing.T, name string) float64 {
	mfs, err := prometheus.DefaultGatherer.Gather()
	if err != nil {
		t.Fatal(err)
	}
	for _, mf := range mfs {
		if mf.GetName() == "etcd_debugging_lease_"+name+"_total" {
			sum := 0.0
			for _, m := range mf.GetMetric() {
				sum += m.GetCounter().GetValue()
			}
			return sum
		}
	}
	t.Fatalf("no metric etcd_debugging_lease_%s_total", name)
	return 0
}

// goroutines counts the goroutines whose stack has a frame of fn, and those created by fn.
func goroutines(fn string) (in, createdBy int) {
	buf := make([]byte, 1<<20)
	for {
		n := runtime.Stack(buf, true)
		if n < len(buf) {
			buf = buf[:n]
			break
		}
		buf = make([]byte, 2*len(buf))
	}
	for _, g := range strings.Split(string(buf), "\n\n") {
		if strings.Contains(g, fn+"(") {
			in++
		}
		if strings.Contains(g, "created by "+fn+" in goroutine") {
			createdBy++
		}
	}
	return in, createdBy
}

const (
	holdTokenFn   = "github.com/mit-pdos/etcd-grove/examples/lib/cluster3.holdToken"
	startMemberFn = "github.com/mit-pdos/etcd-grove/examples/lib/cluster3.StartMember"
)

// peerProbe is what a peer URL answered: the lease handler's two paths (status, and for a 200
// whether the reply is a LeaseInternalResponse with its TimeToLive response and header set, what
// leasePeersOk requires of a 200), leasehttp's own TimeToLiveHTTP's result, and the raft handler's
// probing path.
type peerProbe struct {
	internal, renew, probing int
	internalOk               bool
	ttlErr                   error
}

func probePeer(t *testing.T, addr string, id int64) peerProbe {
	var p peerProbe
	url := "http://" + addr
	post := func(path string, m proto.Message) (int, []byte) {
		b, err := proto.Marshal(m)
		if err != nil {
			t.Fatal(err)
		}
		resp, err := http.Post(url+path, "application/protobuf", bytes.NewReader(b))
		if err != nil {
			t.Fatalf("POST %s%s: %v", url, path, err)
		}
		defer resp.Body.Close()
		var body bytes.Buffer
		body.ReadFrom(resp.Body)
		return resp.StatusCode, body.Bytes()
	}
	var body []byte
	p.internal, body = post(leasehttp.LeaseInternalPrefix, &leasepb.LeaseInternalRequest{
		LeaseTimeToLiveRequest: &pb.LeaseTimeToLiveRequest{ID: id}})
	p.internalOk = true
	if p.internal == http.StatusOK {
		r := &leasepb.LeaseInternalResponse{}
		p.internalOk = proto.Unmarshal(body, r) == nil && r.LeaseTimeToLiveResponse != nil &&
			r.LeaseTimeToLiveResponse.Header != nil
	}
	p.renew, _ = post(leasehttp.LeasePrefix, &pb.LeaseKeepAliveRequest{ID: id})
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, p.ttlErr = leasehttp.TimeToLiveHTTP(ctx, lease.LeaseID(id), false, url+leasehttp.LeaseInternalPrefix,
		http.DefaultTransport)
	cancel()
	resp, err := http.Get(url + "/raft/probing")
	if err != nil {
		t.Fatalf("GET %s/raft/probing: %v", url, err)
	}
	resp.Body.Close()
	p.probing = resp.StatusCode
	return p
}

// checkPeers checks leasePeersOk at every peer URL of cfg.
func checkPeers(t *testing.T, cfg cluster3.Config, id int64, when string) {
	for i, addr := range []string{cfg.Peer1, cfg.Peer2, cfg.Peer3} {
		p := probePeer(t, addr, id)
		t.Logf("%s: peer %d (%s): POST /leases/internal %d, POST /leases %d, TimeToLiveHTTP %v, "+
			"GET /raft/probing %d", when, i+1, addr, p.internal, p.renew, p.ttlErr, p.probing)
		if p.internal == http.StatusOK && !p.internalOk {
			t.Errorf("leasePeersOk FAIL: peer %d answered /leases/internal 200 without a full "+
				"LeaseInternalResponse", i+1)
		}
		if p.internal != http.StatusNotFound || p.renew != http.StatusNotFound {
			t.Errorf("peer %d: lease paths answered %d, %d; the premise's docstring says 404",
				i+1, p.internal, p.renew)
		}
		if p.ttlErr != lease.ErrLeaseNotFound {
			t.Errorf("peer %d: TimeToLiveHTTP returned %v, want ErrLeaseNotFound (404)", i+1, p.ttlErr)
		}
		if p.probing != http.StatusOK {
			t.Errorf("peer %d: /raft/probing answered %d: not the member's raft handler", i+1, p.probing)
		}
	}
}

// dropLessor is the mutant lessor: a Recover that drops, from the snapshot's lease bucket, the
// leases the lessor held before it (as if the snapshot had not carried them), then recovers.
type dropLessor struct {
	lease.Lessor
	dropped []lease.LeaseID
}

func (d *dropLessor) Recover(b backend.Backend, rd lease.RangeDeleter) {
	tx := b.BatchTx()
	tx.LockOutsideApply()
	for _, l := range d.Lessor.Leases() {
		schema.UnsafeDeleteLease(tx, &leasepb.Lease{ID: int64(l.ID)})
		d.dropped = append(d.dropped, l.ID)
	}
	tx.Unlock()
	d.Lessor.Recover(b, rd)
}

// startClusterMutant is cluster3.StartCluster with member 3's lessor replaced by a dropLessor
// before it starts (cluster3.StartMember's steps, without its idle holdToken goroutine).
func startClusterMutant(t *testing.T, cfg cluster3.Config, lg *zap.Logger) []*etcdserver.EtcdServer {
	peers := []types.URLs{{{Scheme: "http", Host: cfg.Peer1}}, {{Scheme: "http", Host: cfg.Peer2}},
		{{Scheme: "http", Host: cfg.Peer3}}}
	cluster := types.URLsMap{cfg.Name1: peers[0], cfg.Name2: peers[1], cfg.Name3: peers[2]}
	names := []string{cfg.Name1, cfg.Name2, cfg.Name3}
	peerAddrs := []string{cfg.Peer1, cfg.Peer2, cfg.Peer3}
	clients := []string{cfg.Client1, cfg.Client2, cfg.Client3}
	var srvs []*etcdserver.EtcdServer
	for i := 0; i < 3; i++ {
		s, err := etcdstart.NewMember(names[i], peers[i], peerAddrs[i], clients[i], cluster,
			cfg.Token, cfg.SnapCount, cfg.SnapCatchUp, lg)
		if err != nil {
			t.Fatal(err)
		}
		if i == 2 {
			*lessorField(s) = &dropLessor{Lessor: lessorOf(s)}
		}
		cl, err := net.Listen("tcp", clients[i])
		if err != nil {
			t.Fatal(err)
		}
		s.Start()
		gs := v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
			MinTime: 5 * time.Second,
		}))
		go gs.Serve(cl)
		srvs = append(srvs, s)
	}
	for _, x := range [][2]string{{cfg.Bridge1, cfg.Client1}, {cfg.Bridge2, cfg.Client2},
		{cfg.Bridge3, cfg.Client3}} {
		if _, err := cluster3.StartBridge(x[0], x[1]); err != nil {
			t.Fatal(err)
		}
	}
	return srvs
}

// obs is what scenario saw.
type obs struct {
	srvs       []*etcdserver.EtcdServer
	ids        []string // the members' ids (memberIDsOf)
	rc         runCounts
	start      time.Time
	g1         clientv3.LeaseID
	applied3   uint64          // member 3's applied index right after g1's grant returned
	be3        backend.Backend // member 3's lessor's backend then
	fillers    []clientv3.LeaseID
	behind3    bool // member 3's lessor lacked the last filler while cut off
	caughtUp   bool // member 3 listed the last filler (run's step 5)
	listedG1   bool // ... and g1 in the same listing (run's check)
	recovered3 bool // member 3's lessor's backend changed (Recover ran on it)
	restore3   uint64
	revoked0   float64 // the revoke counter before the start
	granted0   float64
}

// scenario runs run's steps on the cluster start starts at cfg, with observations between them;
// it fails the test where run would return StartFailed, and does not fail where run's check would
// (the caller judges).
func scenario(t *testing.T, cfg cluster3.Config,
	start func(cluster3.Config, *zap.Logger) []*etcdserver.EtcdServer) *obs {
	t.Chdir(t.TempDir())
	o := &obs{ids: memberIDsOf(t, cfg), rc: newRunCounts()}
	o.revoked0, o.granted0 = leaseCounter(t, "revoked"), leaseCounter(t, "granted")
	o.start = time.Now()
	o.srvs = start(cfg, zap.New(o.rc))
	t.Cleanup(func() {
		for _, s := range o.srvs {
			s.HardStop()
		}
	})
	c3, err := etcdstart.NewClients([]string{cfg.Bridge3}, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { c3.Close() })
	c1, err := etcdstart.NewClients([]string{cfg.Bridge1}, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { c1.Close() })

	// 1. the lease granted through member 3
	g, err := grant(c3)
	if err != nil {
		t.Fatalf("grant through member 3: %v", err)
	}
	o.g1 = g.ID
	o.applied3 = o.srvs[2].AppliedIndex()
	o.be3 = lessorBackend(lessorOf(o.srvs[2]))
	if lessorOf(o.srvs[2]).Lookup(lease.LeaseID(o.g1)) == nil {
		t.Errorf("member 3's lessor lacks g1 right after granting it")
	}

	// 2. member 3 cut off
	cluster3.PeerStep(o.srvs, cluster3.PeerCut, 2, 0)
	cluster3.PeerStep(o.srvs, cluster3.PeerCut, 2, 1)

	// 3. the fillers through member 1
	for i := 0; i < fillers; i++ {
		f, err := grant(c1)
		if err == nil {
			o.fillers = append(o.fillers, f.ID)
		}
	}
	if len(o.fillers) == 0 {
		t.Fatalf("no filler granted")
	}
	last := o.fillers[len(o.fillers)-1]
	o.behind3 = lessorOf(o.srvs[2]).Lookup(lease.LeaseID(last)) == nil

	// 4. mended
	cluster3.PeerStep(o.srvs, cluster3.PeerMend, 2, 0)
	cluster3.PeerStep(o.srvs, cluster3.PeerMend, 2, 1)

	// 5., 6. member 3's listing until it has the last filler
	for p := 0; p < polls && !o.caughtUp; p++ {
		ls, err := leases(c3)
		if err == nil && listed(ls, last) {
			o.caughtUp, o.listedG1 = true, listed(ls, o.g1)
			break
		}
		time.Sleep(pollDelay)
	}
	o.recovered3 = lessorBackend(lessorOf(o.srvs[2])) != o.be3
	o.rc.mu.Lock()
	for _, r := range *o.rc.restores {
		if r.member == o.ids[2] && r.index > o.restore3 {
			o.restore3 = r.index
		}
	}
	o.rc.mu.Unlock()
	t.Logf("run's steps took %v: g1 %x (member 3 applied index %d at its answer), %d fillers, "+
		"member 3 behind while cut %v, caught up %v, listed g1 %v, member 3's lessor recovered %v, "+
		"member 3's highest raft restore %d", time.Since(o.start), o.g1, o.applied3, len(o.fillers),
		o.behind3, o.caughtUp, o.listedG1, o.recovered3, o.restore3)
	return o
}

func realStart(t *testing.T) func(cluster3.Config, *zap.Logger) []*etcdserver.EtcdServer {
	return func(cfg cluster3.Config, lg *zap.Logger) []*etcdserver.EtcdServer {
		srvs, _, ok := cluster3.StartCluster(cfg, lg)
		if !ok {
			t.Fatalf("StartCluster failed")
		}
		return srvs
	}
}

// requireRestore3 fails the test unless member 3 restored, from a snapshot, a lessor holding the
// fillers after g1 was granted: its lessor's backend replaced (Recover ran on member 3), raft's
// restore on member 3 at an index above both member 3's applied index at g1's answer and the
// number of fillers (the snapshot holds them), and member 3 behind while cut off.
func requireRestore3(t *testing.T, o *obs) {
	if !o.caughtUp {
		t.Fatalf("member 3 never listed the last filler")
	}
	if !o.behind3 {
		t.Errorf("member 3's lessor had the last filler while cut off")
	}
	if !o.recovered3 {
		t.Errorf("member 3's lessor was not recovered (its backend is the one before the cut)")
	}
	if o.restore3 <= o.applied3 || o.restore3 <= uint64(fillers) {
		t.Errorf("member 3's raft restore at %d, not above g1's apply (%d) and the fillers (%d)",
			o.restore3, o.applied3, fillers)
	}
}

// TestLeasePeersOk checks leasePeersOk on a cluster3 cluster running Main's steps: at every peer
// URL, before the grant and after the catch-up, a POST to /leases/internal (and to /leases)
// answers 404 (never a 200, let alone one without a full LeaseInternalResponse), leasehttp's
// TimeToLiveHTTP reads it as ErrLeaseNotFound, and the address does serve the member's raft
// handler (/raft/probing answers 200): the premise holds, and it is about the members' listeners.
func TestLeasePeersOk(t *testing.T) {
	cfg := configAt(24100, "lcpeers")
	o := scenario(t, cfg, func(cfg cluster3.Config, lg *zap.Logger) []*etcdserver.EtcdServer {
		srvs := realStart(t)(cfg, lg)
		checkPeers(t, cfg, 1, "after the start")
		return srvs
	})
	checkPeers(t, cfg, int64(o.g1), "after the catch-up")
	requireRestore3(t, o)
}

// TestLeasesNoExpiry checks lease.leasesNoExpiry at TTL 3600 in Main's run: after the catch-up,
// every lessor holds every lease granted in the run (g1 and each filler), with the TTL granted, and
// its lease bucket too; on the leader (whose lessor alone has finite expiries, the others are
// demoted) each lease's remaining time is above TTL minus the run's time, so the expiry loop finds
// none expired (findExpiredLeases returns only leases with Remaining() <= 0) and sends nothing on
// expiredC; and the process's lease_revoked_total counter (every Revoke, the end of a lease the
// expiry loop found) did not move, while lease_granted_total did (every member's Grant).
func TestLeasesNoExpiry(t *testing.T) {
	cfg := configAt(24400, "lcexpiry")
	o := scenario(t, cfg, realStart(t))
	requireRestore3(t, o)
	if !o.listedG1 {
		t.Fatalf("member 3 caught up and did not list g1")
	}
	elapsed := time.Since(o.start)
	all := append([]clientv3.LeaseID{o.g1}, o.fillers...)
	leader := -1
	for i, s := range o.srvs {
		if s.Leader() == s.MemberID() {
			leader = i
		}
	}
	if leader < 0 {
		t.Fatalf("no leader among the members")
	}
	for i, s := range o.srvs {
		le := lessorOf(s)
		minRem := time.Duration(1<<63 - 1)
		for _, id := range all {
			l := le.Lookup(lease.LeaseID(id))
			if l == nil {
				t.Errorf("leasesNoExpiry: member %d's lessor lost lease %x", i+1, id)
				continue
			}
			if l.TTL() != grantTTL {
				t.Errorf("member %d: lease %x TTL %d, want %d", i+1, id, l.TTL(), grantTTL)
			}
			if r := l.Remaining(); r < minRem {
				minRem = r
			}
		}
		tx := s.Backend().ReadTx()
		tx.RLock()
		recs := schema.MustUnsafeGetAllLeases(tx)
		tx.RUnlock()
		inBucket := map[int64]int64{}
		for _, r := range recs {
			inBucket[r.ID] = r.TTL
		}
		for _, id := range all {
			if ttl, ok := inBucket[int64(id)]; !ok || ttl != grantTTL {
				t.Errorf("member %d: lease %x's record %v (present %v)", i+1, id, ttl, ok)
			}
		}
		t.Logf("member %d (leader %v): %d leases in the lessor, %d records, least remaining %v",
			i+1, i == leader, len(le.Leases()), len(recs), minRem)
		if i == leader && minRem < grantTTL*time.Second-elapsed-time.Minute {
			t.Errorf("leader member %d: a lease's remaining time %v below TTL - run time (%v)",
				i+1, minRem, elapsed)
		}
		if minRem <= 0 {
			t.Errorf("leasesNoExpiry FAIL: member %d has an expired lease", i+1)
		}
	}
	revoked := leaseCounter(t, "revoked") - o.revoked0
	granted := leaseCounter(t, "granted") - o.granted0
	t.Logf("run took %v; lease_revoked_total +%v, lease_granted_total +%v (%d leases granted)",
		elapsed, revoked, granted, len(all))
	if revoked != 0 {
		t.Errorf("leasesNoExpiry FAIL: %v leases revoked during the run", revoked)
	}
	// every member applied g1's grant, members 1 and 2 every filler's (member 3 got them by the
	// snapshot, or some by entries)
	if granted < float64(3+2*len(o.fillers)) || granted > float64(3*len(all)) {
		t.Errorf("lease_granted_total +%v, want between %d and %d", granted, 3+2*len(o.fillers),
			3*len(all))
	}
}

// TestCatchUpClaim checks run.spec's claim and that its case is not vacuous: member 3's listing,
// once it lists the last filler, lists g1 (the lease granted through member 3), and member 3 got
// there by restoring its lessor from a snapshot (requireRestore3: Recover ran on member 3's
// lessor, raft restored a snapshot on member 3 above the index member 3 had applied when g1's grant
// returned), so the grant through member 3 came before the restore; and after the restore member
// 3's lessor holds g1 (the listing reads it), recovered from the snapshot's lease bucket.
func TestCatchUpClaim(t *testing.T) {
	cfg := configAt(24500, "lcclaim")
	o := scenario(t, cfg, realStart(t))
	requireRestore3(t, o)
	if !o.listedG1 {
		t.Fatalf("CLAIM FAIL: member 3 caught up and did not list g1")
	}
	if lessorOf(o.srvs[2]).Lookup(lease.LeaseID(o.g1)) == nil {
		t.Errorf("member 3's recovered lessor lacks g1")
	}
	o.rc.mu.Lock()
	t.Logf("snapshots sent to member 3: %d; restored lease stores: %d", o.rc.sentTo[o.ids[2]],
		o.rc.n[cntLeaseRestore])
	o.rc.mu.Unlock()
}

// TestCatchUpMutant runs Main's steps with member 3's lessor a dropLessor (its Recover drops from
// the snapshot's lease bucket the leases it held, as if the snapshot had not carried them): the
// restore happens as in the real run, and run's check then fails (member 3 lists the last filler
// but not g1), so the check sees a lease the snapshot does not carry.
func TestCatchUpMutant(t *testing.T) {
	cfg := configAt(24200, "lcmutant")
	o := scenario(t, cfg, func(cfg cluster3.Config, lg *zap.Logger) []*etcdserver.EtcdServer {
		return startClusterMutant(t, cfg, lg)
	})
	requireRestore3(t, o)
	d := lessorOf(o.srvs[2]).(*dropLessor)
	t.Logf("the mutant's Recover dropped %x", d.dropped)
	if o.listedG1 {
		t.Fatalf("mutant: member 3 still listed g1 (dropped %x): the check does not see the loss",
			d.dropped)
	}
}

// TestHoldTokenPerMember checks cluster3.StartMember's go holdToken(): each call adds exactly
// one goroutine running holdToken, and two goroutines created by StartMember (holdToken and the
// gRPC server's Serve), which are still there after the cluster has run (holdToken never returns).
func TestHoldTokenPerMember(t *testing.T) {
	t.Chdir(t.TempDir())
	cfg := configAt(24300, "lchold")
	peers := []types.URLs{{{Scheme: "http", Host: cfg.Peer1}}, {{Scheme: "http", Host: cfg.Peer2}},
		{{Scheme: "http", Host: cfg.Peer3}}}
	cluster := types.URLsMap{cfg.Name1: peers[0], cfg.Name2: peers[1], cfg.Name3: peers[2]}
	names := []string{cfg.Name1, cfg.Name2, cfg.Name3}
	peerAddrs := []string{cfg.Peer1, cfg.Peer2, cfg.Peer3}
	clients := []string{cfg.Client1, cfg.Client2, cfg.Client3}
	h0, _ := goroutines(holdTokenFn)
	_, c0 := goroutines(startMemberFn)
	n0 := runtime.NumGoroutine()
	var srvs []*etcdserver.EtcdServer
	t.Cleanup(func() {
		for _, s := range srvs {
			s.HardStop()
		}
	})
	for i := 0; i < 3; i++ {
		s, err := cluster3.StartMember(names[i], peers[i], peerAddrs[i], clients[i], cluster,
			cfg.Token, cfg.SnapCount, cfg.SnapCatchUp, zap.NewNop())
		if err != nil {
			t.Fatal(err)
		}
		srvs = append(srvs, s)
		h, _ := goroutines(holdTokenFn)
		_, c := goroutines(startMemberFn)
		t.Logf("after member %d: holdToken goroutines +%d, created by StartMember +%d, all +%d",
			i+1, h-h0, c-c0, runtime.NumGoroutine()-n0)
		if h-h0 != i+1 || c-c0 != 2*(i+1) {
			t.Errorf("after member %d: holdToken +%d (want %d), created by StartMember +%d (want %d)",
				i+1, h-h0, i+1, c-c0, 2*(i+1))
		}
	}
	// the cluster serves: a grant through member 1's client address, then the count again
	c, err := etcdstart.NewClients([]string{cfg.Client1}, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	if _, err := grant(c); err != nil {
		t.Fatalf("grant: %v", err)
	}
	h, _ := goroutines(holdTokenFn)
	if h-h0 != 3 {
		t.Errorf("after a grant: holdToken goroutines +%d, want 3", h-h0)
	}
}
