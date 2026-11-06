package leaseexpiry

// The Test phase of revoke-open (notes/revoke-open-plan.md, "Test (2026-11-06)"): Go tests that the
// claims and premises of the restated specs hold of etcd's real EtcdServer.revokeExpiredLeases (the
// arm of run that receives the lessor's expired leases), of GoAttach, and of the goroutine
// accounting the levels (srvRevokeLevels, threadBound >= 4) rest on. Each test starts one member of
// its own (addresses 127.0.0.1:247xx, not Main's), with the lessor's expiry channel observed and,
// where said, its Revoke slowed (a slow apply, as on a slow disk); no etcd code is changed:
//
//   - TestRevokeBothArms: 40 leases of TTL 1 expire; every one is revoked, each delivered lease is
//     tried exactly once by the round (success: etcd_debugging_server_lease_expired_total; failure:
//     the "failed to revoke lease" warning, here ErrLeaseNotFound for a lease re-delivered while its
//     revoke was in flight), and the slices on expiredC meet lease.expiredLeases;
//   - TestRevokeGoroutines: Q9's accounting, sampled by stack frame through the same run: every
//     goroutine of the revocation is GoAttach's, the outer one created by run's goroutine, the inner
//     ones by an outer one (depth two below run: levels 1..3 of run's token), no inner one creates
//     a goroutine, and a round's inner goroutines holding a slot of its channel c are at most
//     maxPendingRevokes;
//   - TestRevokeStop: Stop during a round (the outer blocked on a full c) returns, no goroutine of
//     the revocation is left, and nothing panics;
//   - TestGoAttachStop: GoAttach.spec's two branches, nested once as the revocation nests it: a
//     GoAttach'd goroutine (and one it GoAttaches) runs and delays Stop until it ends (counted by
//     s.wg), while a plain `go` goroutine does not (the mutant: the check sees the difference); after
//     Stop, GoAttach returns and f never runs.
//
// The file's name sorts before leaseexpiry_test.go on purpose (the Scope's Q11 called it
// revoke_stats_test.go): go test runs a package's tests in the order of its files, and
// TestMainRun leaves Main's member running with its relative DataDir in a temporary directory
// removed when TestMainRun ends; that member's file purge (every 30s, purgeFileInterval) then fails
// and calls zap's Fatal, which exits the test binary silently (Main's logger is a Nop) in whatever
// test is running 30s after Main's start. Run first, these tests end before Main starts.

import (
	"bufio"
	"context"
	"fmt"
	"os"
	"reflect"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"
	"unsafe"

	"github.com/prometheus/client_golang/prometheus"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/lease"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

const (
	srvPkg     = "go.etcd.io/etcd/server/v3/etcdserver"
	outerFn    = srvPkg + ".(*EtcdServer).revokeExpiredLeases.func1"
	innerFn    = outerFn + ".1.1"
	goAttachFn = srvPkg + ".(*EtcdServer).GoAttach"
	runFn      = srvPkg + ".(*EtcdServer).run"
	// maxPendingRevokes is etcdserver's constant (server.go), c's capacity
	maxPendingRevokes = 16
	nLeases           = 40
)

// field is the address of EtcdServer's unexported field name (a test-only abstraction function,
// as leasecatchup's lessorField).
func field(s *etcdserver.EtcdServer, name string) unsafe.Pointer {
	return unsafe.Pointer(reflect.ValueOf(s).Elem().FieldByName(name).UnsafeAddr())
}

// obsLessor is the server's lessor with its expiry channel observed: every slice the real lessor
// sends on expiredC is recorded (its lease ids, read at delivery) and forwarded, unchanged, on the
// channel the server's run reads; Revoke (the apply of a LeaseRevoke) first sleeps delay.
type obsLessor struct {
	lease.Lessor
	delay  time.Duration
	out    chan []*lease.Lease
	done   chan struct{}
	mu     sync.Mutex
	slices [][]*lease.Lease
	ids    [][]lease.LeaseID
	bad    []string // slices that break lease.expiredLeases
}

func (l *obsLessor) Revoke(id lease.LeaseID) error {
	time.Sleep(l.delay)
	return l.Lessor.Revoke(id)
}

func (l *obsLessor) ExpiredLeasesC() <-chan []*lease.Lease { return l.out }

func (l *obsLessor) forward() {
	in := l.Lessor.ExpiredLeasesC()
	for {
		select {
		case ls := <-in:
			l.mu.Lock()
			var ids []lease.LeaseID
			if len(ls) == 0 {
				l.bad = append(l.bad, "an empty slice")
			}
			for i, p := range ls {
				if p == nil {
					l.bad = append(l.bad, fmt.Sprintf("element %d nil", i))
					continue
				}
				ids = append(ids, p.ID)
			}
			l.slices, l.ids = append(l.slices, ls), append(l.ids, ids)
			l.mu.Unlock()
			select {
			case l.out <- ls:
			case <-l.done:
				return
			}
		case <-l.done:
			return
		}
	}
}

// delivered is the number of leases delivered on expiredC, and the slices' sizes.
func (l *obsLessor) delivered() (n int, sizes []int) {
	l.mu.Lock()
	defer l.mu.Unlock()
	for _, ids := range l.ids {
		n += len(ids)
		sizes = append(sizes, len(ids))
	}
	return n, sizes
}

// member is one started member with an obsLessor, its client and its warnings.
type member struct {
	s    *etcdserver.EtcdServer
	le   *obsLessor
	cli  *clientv3.Client
	logs *observer.ObservedLogs
}

// startMember is etcdstart.StartServer's member (BuildServer, then Start), its lessor replaced
// before Start by an obsLessor and its applier rebuilt over it (NewUberApplier, as applySnapshot
// rebuilds it), then Serve and a client.
func startMember(t *testing.T, name, peerAddr, clientAddr string, delay time.Duration) *member {
	t.Chdir(t.TempDir())
	core, logs := observer.New(zapcore.WarnLevel)
	lg := zap.New(core)
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := etcdstart.BuildServer(name, peer, clientAddr, types.URLsMap{name: peer}, name,
		etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
	if err != nil {
		t.Fatal(err)
	}
	lp := (*lease.Lessor)(field(s, "lessor"))
	le := &obsLessor{Lessor: *lp, delay: delay, out: make(chan []*lease.Lease, 16),
		done: make(chan struct{})}
	*lp = le
	*(*apply.UberApplier)(field(s, "uberApply")) = s.NewUberApplier()
	go le.forward()
	s.Start()
	m := &member{s: s, le: le, logs: logs}
	t.Cleanup(func() {
		s.HardStop()
		close(le.done)
	})
	if err := etcdstart.Serve(s, clientAddr); err != nil {
		t.Fatal(err)
	}
	m.cli, err = etcdstart.NewClient(clientAddr, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { m.cli.Close() })
	return m
}

// grantAll grants n leases of grantTTL at once and returns their ids.
func grantAll(t *testing.T, cli *clientv3.Client, n int) map[lease.LeaseID]bool {
	var mu sync.Mutex
	ids := map[lease.LeaseID]bool{}
	var wg sync.WaitGroup
	for i := 0; i < n; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
			defer cancel()
			g, err := cli.Grant(ctx, grantTTL)
			if err != nil {
				t.Errorf("grant: %v", err)
				return
			}
			mu.Lock()
			ids[lease.LeaseID(g.ID)] = true
			mu.Unlock()
		}()
	}
	wg.Wait()
	if len(ids) != n {
		t.Fatalf("%d leases granted, want %d", len(ids), n)
	}
	return ids
}

// counter is the process's counter name (summed over its labels).
func counter(t *testing.T, name string) float64 {
	mfs, err := prometheus.DefaultGatherer.Gather()
	if err != nil {
		t.Fatal(err)
	}
	for _, mf := range mfs {
		if mf.GetName() == name {
			sum := 0.0
			for _, m := range mf.GetMetric() {
				sum += m.GetCounter().GetValue()
			}
			return sum
		}
	}
	t.Fatalf("no metric %s", name)
	return 0
}

const (
	expiredMetric = "etcd_debugging_server_lease_expired_total" // leaseExpired.Inc(), the success arm
	revokedMetric = "etcd_debugging_lease_revoked_total"        // lessor.Revoke's success
)

// warns is the number of logged warnings with message msg, and their "error" fields.
func warns(logs *observer.ObservedLogs, msg string) (int, map[string]int) {
	errs := map[string]int{}
	es := logs.FilterMessage(msg).All()
	for _, e := range es {
		errs[fmt.Sprint(e.ContextMap()["error"])]++
	}
	return len(es), errs
}

// goroutine is one goroutine of a stack dump: its id, its frames' functions (innermost first)
// with their lines, and its creator.
type goroutine struct {
	id        int
	fns       []string
	lines     []int
	creator   string
	creatorID int
}

func (g goroutine) frame(fn string) int {
	for i, f := range g.fns {
		if f == fn {
			return i
		}
	}
	return -1
}

// dump parses runtime.Stack of every goroutine.
func dump() []goroutine {
	buf := make([]byte, 1<<20)
	for {
		n := runtime.Stack(buf, true)
		if n < len(buf) {
			buf = buf[:n]
			break
		}
		buf = make([]byte, 2*len(buf))
	}
	var gs []goroutine
	for _, blk := range strings.Split(string(buf), "\n\n") {
		ls := strings.Split(blk, "\n")
		var g goroutine
		if _, err := fmt.Sscanf(ls[0], "goroutine %d", &g.id); err != nil {
			continue
		}
		for i := 1; i+1 < len(ls); i += 2 {
			f, loc := ls[i], strings.TrimSpace(ls[i+1])
			line := 0
			if c := strings.LastIndex(loc, ":"); c >= 0 {
				line, _ = strconv.Atoi(strings.Fields(loc[c+1:])[0])
			}
			if strings.HasPrefix(f, "created by ") {
				rest := strings.TrimPrefix(f, "created by ")
				if k := strings.Index(rest, " in goroutine "); k >= 0 {
					g.creator = rest[:k]
					g.creatorID, _ = strconv.Atoi(rest[k+len(" in goroutine "):])
				} else {
					g.creator = rest
				}
				continue
			}
			if p := strings.LastIndex(f, "("); p > 0 {
				f = f[:p]
			}
			g.fns, g.lines = append(g.fns, f), append(g.lines, line)
		}
		gs = append(gs, g)
	}
	return gs
}

// releaseLine is the line of the inner goroutine's `<-c` in server.go (read from the source the
// stack names): an inner goroutine whose frame is above it holds a slot of its round's c.
func releaseLine(t *testing.T, file string) int {
	f, err := os.Open(file)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	n, in := 0, false
	for sc.Scan() {
		n++
		l := strings.TrimSpace(sc.Text())
		if strings.HasPrefix(l, "func (s *EtcdServer) revokeExpiredLeases(") {
			in = true
		}
		if in && l == "<-c" {
			return n
		}
	}
	t.Fatalf("no `<-c` in revokeExpiredLeases in %s", file)
	return 0
}

func serverGo(t *testing.T) string {
	pc := reflect.ValueOf((*etcdserver.EtcdServer).GoAttach).Pointer()
	file, _ := runtime.FuncForPC(pc).FileLine(pc)
	return file
}

// accounting is what the sampler saw of the revocation's goroutines.
type accounting struct {
	samples                        int
	peakOuter, peakInner, peakBusy int // live outer, inner, inner holding a slot (all rounds)
	peakBusyRound                  int // inner holding a slot of one round's c
	outers, inners                 map[int]bool
	others                         map[int]bool // goroutines seen that are neither
	errs                           []string
}

// sample records one dump into a.
func (a *accounting) sample(rel int) {
	gs := dump()
	a.samples++
	outer, inner, busy := 0, 0, 0
	busyBy := map[int]int{}
	runs := map[int]bool{}
	for _, g := range gs {
		if g.frame(runFn) >= 0 {
			runs[g.id] = true
		}
	}
	for _, g := range gs {
		fi, fo := g.frame(innerFn), g.frame(outerFn)
		switch {
		case fi >= 0:
			inner++
			a.inners[g.id] = true
			if g.lines[fi] < rel {
				busy++
				busyBy[g.creatorID]++
			}
			if g.creator != goAttachFn {
				a.errs = append(a.errs, fmt.Sprintf("inner goroutine %d created by %s", g.id, g.creator))
			}
			if a.others[g.creatorID] || runs[g.creatorID] {
				a.errs = append(a.errs, fmt.Sprintf("inner goroutine %d created by goroutine %d, not "+
					"an outer one", g.id, g.creatorID))
			}
		case fo >= 0:
			outer++
			a.outers[g.id] = true
			if g.creator != goAttachFn || !runs[g.creatorID] {
				a.errs = append(a.errs, fmt.Sprintf("outer goroutine %d created by %s in goroutine "+
					"%d, not GoAttach in run's", g.id, g.creator, g.creatorID))
			}
		default:
			// (a goroutine GoAttach just created may not yet be in its f)
			if !a.outers[g.id] && !a.inners[g.id] && g.creator != goAttachFn {
				a.others[g.id] = true
			}
			if strings.HasPrefix(g.creator, outerFn) {
				a.errs = append(a.errs, fmt.Sprintf("goroutine %d created by %s", g.id, g.creator))
			}
		}
	}
	for _, g := range gs {
		if g.frame(innerFn) >= 0 && a.inners[g.creatorID] {
			a.errs = append(a.errs, fmt.Sprintf("inner goroutine %d created by inner %d", g.id,
				g.creatorID))
		}
	}
	a.peakOuter, a.peakInner, a.peakBusy = max(a.peakOuter, outer), max(a.peakInner, inner),
		max(a.peakBusy, busy)
	for _, n := range busyBy {
		a.peakBusyRound = max(a.peakBusyRound, n)
	}
}

func (a *accounting) live() (outer, inner int) {
	for _, g := range dump() {
		if g.frame(innerFn) >= 0 {
			inner++
		} else if g.frame(outerFn) >= 0 {
			outer++
		}
	}
	return
}

// sampler samples every 2ms until stop is closed.
func sampler(rel int, a *accounting, stop chan struct{}, done chan struct{}) {
	defer close(done)
	tk := time.NewTicker(2 * time.Millisecond)
	defer tk.Stop()
	for {
		select {
		case <-stop:
			return
		case <-tk.C:
			a.sample(rel)
		}
	}
}

func newAccounting() *accounting {
	return &accounting{outers: map[int]bool{}, inners: map[int]bool{}, others: map[int]bool{}}
}

// armsRun is what runArms (TestRevokeBothArms's scenario) saw.
type armsRun struct {
	m                  *member
	granted            map[lease.LeaseID]bool
	expired0, revoked0 float64
	acc                *accounting
	took               time.Duration
	expired, revoked   float64
	failed             int
	failErrs           map[string]int
	delivered          int
	sizes              []int
}

func runArms(t *testing.T, name, peerAddr, clientAddr string) *armsRun {
	r := &armsRun{acc: newAccounting()}
	// 250ms per applied revoke: 40 revokes take 10s, more than the lessor's retry interval (7s, the
	// server's ReqTimeout at 10 ticks of 100ms), so leases still in the lessor 7s after their
	// delivery are delivered again, in a round whose revokes find them gone
	r.m = startMember(t, name, peerAddr, clientAddr, 250*time.Millisecond)
	rel := releaseLine(t, serverGo(t))
	r.expired0, r.revoked0 = counter(t, expiredMetric), counter(t, revokedMetric)
	stop, done := make(chan struct{}), make(chan struct{})
	go sampler(rel, r.acc, stop, done)
	start := time.Now()
	r.granted = grantAll(t, r.m.cli, nLeases)
	// until the lessor is empty and no goroutine of the revocation is left
	deadline := time.Now().Add(90 * time.Second)
	for {
		o, i := r.acc.live()
		if len(r.m.le.Lessor.Leases()) == 0 && o == 0 && i == 0 {
			break
		}
		if time.Now().After(deadline) {
			close(stop)
			<-done
			t.Fatalf("after 90s: %d leases left, %d outer and %d inner goroutines live",
				len(r.m.le.Lessor.Leases()), o, i)
		}
		time.Sleep(20 * time.Millisecond)
	}
	close(stop)
	<-done
	r.took = time.Since(start)
	r.expired = counter(t, expiredMetric) - r.expired0
	r.revoked = counter(t, revokedMetric) - r.revoked0
	r.failed, r.failErrs = warns(r.m.logs, "failed to revoke lease")
	r.delivered, r.sizes = r.m.le.delivered()
	return r
}

// TestRevokeBothArms: 40 leases of TTL 1 granted at once; every one is revoked, by the expiry arm
// of run (revokeExpiredLeases), each exactly once with success (lease_expired_total +40, the
// lessor's revoked_total +40); every lease delivered on expiredC is tried exactly once by its round
// (successes + "failed to revoke lease" warnings = leases delivered), so the leases re-delivered
// while their first revoke was in flight reach the failure arm (ErrLeaseNotFound); and every slice
// on expiredC is non-empty, of non-nil leases, each one granted here (lease.expiredLeases).
func TestRevokeBothArms(t *testing.T) {
	r := runArms(t, "revokearms", "127.0.0.1:24711", "127.0.0.1:24721")
	notLeader, _ := warns(r.m.logs, "Ignore the lease revoking request because current member isn't a leader")
	t.Logf("took %v; slices on expiredC %v (%d leases); lease_expired_total +%v, revoked_total +%v; "+
		"failed revokes %d %v; not-leader rounds %d", r.took, r.sizes, r.delivered, r.expired,
		r.revoked, r.failed, r.failErrs, notLeader)
	r.m.le.mu.Lock()
	for _, b := range r.m.le.bad {
		t.Errorf("expiredLeases FAIL: %s", b)
	}
	for i, ids := range r.m.le.ids {
		for j, id := range ids {
			if !r.granted[id] {
				t.Errorf("expiredLeases FAIL: slice %d element %d: lease %x not granted here", i, j, id)
			}
			if r.m.le.slices[i][j].ID != id {
				t.Errorf("lease %x's ID changed to %x", id, r.m.le.slices[i][j].ID)
			}
		}
	}
	r.m.le.mu.Unlock()
	if r.expired != nLeases || r.revoked != nLeases {
		t.Errorf("lease_expired_total +%v, revoked_total +%v, want %d each", r.expired, r.revoked,
			nLeases)
	}
	if int(r.expired)+r.failed != r.delivered {
		t.Errorf("successes %v + failures %d != %d leases delivered: a delivered lease not tried "+
			"exactly once", r.expired, r.failed, r.delivered)
	}
	if r.failed == 0 {
		t.Errorf("the failure arm was not reached (no lease re-delivered while in flight)")
	}
	for e := range r.failErrs {
		if e != lease.ErrLeaseNotFound.Error() {
			t.Errorf("a revoke failed with %q, want only %q", e, lease.ErrLeaseNotFound)
		}
	}
	if notLeader != 0 {
		t.Errorf("%d rounds found the single member not leader", notLeader)
	}
}

// TestRevokeGoroutines: Q9's accounting in TestRevokeBothArms's scenario, by stack frame, every
// 2ms: every goroutine of the revocation is created by GoAttach (so counted by s.wg); each outer
// one by run's goroutine (level 1 of run's token), each inner one by an outer one, never by run or
// another goroutine (level 1 of the outer's fresh token), and no goroutine is created by either
// directly; a round's inner goroutines holding a slot of its c (before `<-c`) are at most
// maxPendingRevokes, and that bound is reached (the 40-lease round blocks on c).
func TestRevokeGoroutines(t *testing.T) {
	r := runArms(t, "revokegor", "127.0.0.1:24712", "127.0.0.1:24722")
	a := r.acc
	t.Logf("%d samples over %v: peak live outer %d, inner %d, inner holding a slot %d (one round: "+
		"%d); distinct outer %d, inner %d; slices %v", a.samples, r.took, a.peakOuter, a.peakInner,
		a.peakBusy, a.peakBusyRound, len(a.outers), len(a.inners), r.sizes)
	for i, e := range a.errs {
		if i == 10 {
			t.Errorf("... %d more", len(a.errs)-10)
			break
		}
		t.Error(e)
	}
	if a.peakBusyRound > maxPendingRevokes {
		t.Errorf("a round had %d inner goroutines holding a slot, above %d", a.peakBusyRound,
			maxPendingRevokes)
	}
	if a.peakBusyRound != maxPendingRevokes {
		t.Errorf("the bound was not reached (peak %d): the test did not block a round on c",
			a.peakBusyRound)
	}
	if len(a.outers) > len(r.sizes) {
		t.Errorf("%d outer goroutines for %d slices delivered", len(a.outers), len(r.sizes))
	}
	if len(a.inners) > r.delivered {
		t.Errorf("%d inner goroutines for %d leases delivered", len(a.inners), r.delivered)
	}
}

// TestRevokeStop: Stop while a round's outer goroutine is blocked on a full c (16 inner goroutines
// in flight, the applies slowed to 300ms each). Stop returns, and then no goroutine of the
// revocation is left (run's deferred s.wg.Wait waited for them all); the round is cut (fewer than
// 40 leases revoked); nothing panics (a panic in any goroutine would end the test binary).
func TestRevokeStop(t *testing.T) {
	m := startMember(t, "revokestop", "127.0.0.1:24713", "127.0.0.1:24723", 300*time.Millisecond)
	rel := releaseLine(t, serverGo(t))
	expired0 := counter(t, expiredMetric)
	grantAll(t, m.cli, nLeases)
	a := newAccounting()
	deadline := time.Now().Add(60 * time.Second)
	for a.peakBusyRound < maxPendingRevokes {
		if time.Now().After(deadline) {
			t.Fatalf("no round blocked on c within 60s")
		}
		time.Sleep(5 * time.Millisecond)
		a.sample(rel)
	}
	o, i := a.live()
	t.Logf("before Stop: %d outer, %d inner goroutines live", o, i)
	stopped := make(chan struct{})
	start := time.Now()
	go func() {
		m.s.Stop()
		close(stopped)
	}()
	select {
	case <-stopped:
	case <-time.After(60 * time.Second):
		t.Fatalf("Stop did not return in 60s")
	}
	o, i = a.live()
	expired := counter(t, expiredMetric) - expired0
	failed, errs := warns(m.logs, "failed to revoke lease")
	skipped, _ := warns(m.logs, "server has stopped; skipping GoAttach")
	t.Logf("Stop took %v; after it: %d outer, %d inner goroutines; lease_expired_total +%v, "+
		"failed revokes %d %v, skipped GoAttach %d, leases left %d", time.Since(start), o, i,
		expired, failed, errs, skipped, len(m.le.Lessor.Leases()))
	for _, e := range a.errs {
		t.Error(e)
	}
	if o != 0 || i != 0 {
		t.Errorf("after Stop: %d outer and %d inner goroutines of the revocation left", o, i)
	}
	if expired >= nLeases {
		t.Errorf("all %d leases revoked: Stop did not cut the round", nLeases)
	}
}

// TestGoAttachStop: GoAttach.spec on a running member, nested once as the revocation nests it.
// Before Stop, f runs in a goroutine, which GoAttaches g; GoAttach returns without waiting for f;
// Stop does not return while f or g runs (both counted by s.wg) and returns once they end. The
// mutant: a goroutine started by a plain `go` (not counted) is still running when Stop returns.
// After Stop, GoAttach returns, warns "server has stopped; skipping GoAttach", and f never runs.
func TestGoAttachStop(t *testing.T) {
	m := startMember(t, "goattach", "127.0.0.1:24714", "127.0.0.1:24724", 0)
	releaseF, releaseG, releasePlain := make(chan struct{}), make(chan struct{}), make(chan struct{})
	fRan, gRan, gDone, plainDone := make(chan struct{}), make(chan struct{}), make(chan struct{}),
		make(chan struct{})
	m.s.GoAttach(func() {
		close(fRan)
		m.s.GoAttach(func() {
			close(gRan)
			<-releaseG
			close(gDone)
		})
		<-releaseF
	})
	go func() {
		<-releasePlain
		close(plainDone)
	}()
	for _, c := range []chan struct{}{fRan, gRan} {
		select {
		case <-c:
		case <-time.After(10 * time.Second):
			t.Fatalf("a GoAttach'd function did not run")
		}
	}
	stopped := make(chan struct{})
	go func() {
		m.s.Stop()
		close(stopped)
	}()
	select {
	case <-stopped:
		t.Fatalf("Stop returned while two GoAttach'd goroutines ran")
	case <-time.After(3 * time.Second):
	}
	close(releaseF)
	select {
	case <-stopped:
		t.Fatalf("Stop returned while g (GoAttach'd by f) ran")
	case <-time.After(2 * time.Second):
	}
	close(releaseG)
	select {
	case <-stopped:
	case <-time.After(60 * time.Second):
		t.Fatalf("Stop did not return after f and g ended")
	}
	select {
	case <-gDone:
	default:
		t.Errorf("Stop returned before g ended")
	}
	select {
	case <-plainDone:
		t.Errorf("mutant: the plain goroutine ended")
	default:
		t.Logf("mutant: a plain `go` goroutine is still running after Stop (not counted by s.wg)")
	}
	close(releasePlain)

	ran := make(chan struct{})
	m.s.GoAttach(func() { close(ran) })
	select {
	case <-ran:
		t.Errorf("GoAttach after Stop ran f")
	case <-time.After(2 * time.Second):
	}
	if n, _ := warns(m.logs, "server has stopped; skipping GoAttach"); n != 1 {
		t.Errorf("%d skipping-GoAttach warnings, want 1", n)
	}
}
