//go:build leasesnap

// Package leasesnap tests, against the real Go code, the claims of the S2–S4 specs ("snapshots
// carry leases", notes/lease-expiry-plan.md, "S2–S4 Test (2026-11-05)"). No proof; not translated.
//
// Not compiled in this repository's examples module (whose go.mod lacks the integration
// framework's dependencies): run it in a scratch checkout of the etcd fork at etc/goose.py's etcd
// revision (673da07c8fab), as a package of etcd's tests module:
//
//	export PATH=$PATH:/usr/local/go/bin GOTOOLCHAIN=go1.27.3 TMPDIR=/shared/tmp
//	git clone -q https://github.com/upamanyus/etcd $TMPDIR/leasesnap-etcd
//	git -C $TMPDIR/leasesnap-etcd checkout -q 673da07c8fabc5a544d0017ff0cc241802bcd9b1
//	mkdir $TMPDIR/leasesnap-etcd/tests/integration/leasesnap
//	cp leasesnap_test.go $TMPDIR/leasesnap-etcd/tests/integration/leasesnap/
//	cd $TMPDIR/leasesnap-etcd/tests && go test -tags leasesnap ./integration/leasesnap -count=1 -v
//	rm -rf $TMPDIR/leasesnap-etcd
//
// The build tag keeps it out of the examples module's `go build ./...`/`go vet ./...`.
//
// The claims (the specs' names):
//
//  1. lease.lessor.Recover.spec / initAndRecover: after a restore each recovered lease's TTL is
//     max(record TTL, this member's minLeaseTTL); the recovered ids are exactly the records';
//     an id live before and in the records stays live.
//  2. lease.leaseTTLAt_ge_req: a lease's TTL on any member, at any time (GrantedTTL as
//     TimeToLive reports it, and the lessor's TTL), is >= the TTL its grant requested; across
//     restores in a three-member cluster whose members have different ElectionTicks (so different
//     minLeaseTTL). And GrantedTTL differs between members and across one member's restore.
//  3. lessor.Grant.spec: the granted TTL is max(request, minLeaseTTL) (grantTTL).
//  4. The image's lease bucket (imageLeasesAt, bkRestAtL's leaseTTLsAbove): one record per lease
//     of the applied table, TTL >= the request.
package leasesnap

import (
	"context"
	"reflect"
	"sort"
	"testing"
	"time"
	"unsafe"

	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// lessorOf reads EtcdServer's unexported lessor field (a test-only abstraction function: the
// member's lessor as the specs' lessorAt describes it).
func lessorOf(s *etcdserver.EtcdServer) lease.Lessor {
	f := reflect.ValueOf(s).Elem().FieldByName("lessor")
	return *(*lease.Lessor)(unsafe.Pointer(f.UnsafeAddr()))
}

// minLeaseTTL is server.go's formula: ceil((3*ElectionTicks/2) * TickMs) in seconds.
func minLeaseTTL(m *integration.Member) int64 {
	d := time.Duration((3*m.ElectionTicks)/2) * time.Duration(m.TickMs) * time.Millisecond
	s := int64(d / time.Second)
	if d%time.Second != 0 {
		s++
	}
	return s
}

// records is the member's lease bucket (the image the snapshot carries, on a leader; the image
// received, on a member that restored one), as MustUnsafeGetAllLeases reads it.
func records(be backend.Backend) map[int64]int64 {
	be.ForceCommit()
	tx := be.ReadTx()
	tx.RLock()
	defer tx.RUnlock()
	out := map[int64]int64{}
	for _, l := range schema.MustUnsafeGetAllLeases(tx) {
		if _, dup := out[l.ID]; dup {
			panic("duplicate lease record")
		}
		out[l.ID] = l.TTL
	}
	return out
}

func lessorTTLs(le lease.Lessor) map[int64]int64 {
	out := map[int64]int64{}
	for _, l := range le.Leases() {
		out[int64(l.ID)] = l.TTL()
	}
	return out
}

func ids(m map[int64]int64) []int64 {
	var r []int64
	for k := range m {
		r = append(r, k)
	}
	sort.Slice(r, func(i, j int) bool { return r[i] < r[j] })
	return r
}

func max64(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
}

type harness struct {
	t    *testing.T
	clus *integration.Cluster
	req  map[int64]int64 // lease id -> requested TTL
	ctx  context.Context
}

func (h *harness) client(i int) *clientv3.Client {
	c, err := integration.NewClientV3(h.clus.Members[i])
	if err != nil {
		h.t.Fatal(err)
	}
	h.t.Cleanup(func() { c.Close() })
	return c
}

func (h *harness) leaderIdx() int { return h.clus.WaitLeader(h.t) }

func (h *harness) moveLeader(to int) {
	t := h.t
	lead := h.leaderIdx()
	if lead == to {
		return
	}
	ctx, cancel := context.WithTimeout(h.ctx, 10*time.Second)
	defer cancel()
	ls := h.clus.Members[lead].Server
	if err := ls.MoveLeader(ctx, uint64(ls.MemberID()), uint64(h.clus.Members[to].Server.MemberID())); err != nil {
		t.Fatalf("MoveLeader to %d: %v", to, err)
	}
	for i := 0; i < 500 && h.leaderIdx() != to; i++ {
		time.Sleep(20 * time.Millisecond)
	}
	if h.leaderIdx() != to {
		t.Fatalf("leader is %d, want %d", h.leaderIdx(), to)
	}
}

// grant grants through member i and checks claim 3 on the answer.
func (h *harness) grant(i int, ttl int64) int64 {
	resp, err := h.client(i).Grant(h.ctx, ttl)
	if err != nil {
		h.t.Fatalf("grant via m%d: %v", i, err)
	}
	want := max64(ttl, minLeaseTTL(h.clus.Members[i]))
	h.t.Logf("claim 3: Grant(TTL %d) via m%d (minLeaseTTL %d): id %x, granted TTL %d (want max = %d)",
		ttl, i, minLeaseTTL(h.clus.Members[i]), resp.ID, resp.TTL, want)
	if resp.TTL != want {
		h.t.Errorf("claim 3 FAIL: granted %d, want %d", resp.TTL, want)
	}
	h.req[int64(resp.ID)] = ttl
	return int64(resp.ID)
}

// waitApplied waits until every running member has applied the leader's applied index.
func (h *harness) waitApplied(running []int) {
	lead := h.clus.Members[h.leaderIdx()].Server
	want := lead.AppliedIndex()
	for _, i := range running {
		for k := 0; h.clus.Members[i].Server.AppliedIndex() < want; k++ {
			if k > 1000 {
				h.t.Fatalf("m%d stuck at applied %d < %d", i, h.clus.Members[i].Server.AppliedIndex(), want)
			}
			time.Sleep(10 * time.Millisecond)
		}
	}
}

// checkMember checks, on member i: claim 2 (lessor TTL >= request), claim 4 (bucket = one record
// per lessor lease, TTL >= request), and, when grantsApplied, claim 3's lessor side (TTL =
// max(request, own min)) for the ids in grantsApplied.
func (h *harness) checkMember(i int, label string) (map[int64]int64, map[int64]int64) {
	m := h.clus.Members[i]
	ttls := lessorTTLs(lessorOf(m.Server))
	recs := records(m.Server.Backend())
	h.t.Logf("%s m%d (minLeaseTTL %d): lessor %v, bucket %v", label, i, minLeaseTTL(m), ttls, recs)
	if !reflect.DeepEqual(ids(ttls), ids(recs)) {
		h.t.Errorf("claim 4 FAIL on m%d: lessor ids %v, bucket ids %v", i, ids(ttls), ids(recs))
	}
	for id, t := range ttls {
		if r, ok := h.req[id]; ok && t < r {
			h.t.Errorf("claim 2 FAIL on m%d: lease %x TTL %d < request %d", i, id, t, r)
		}
	}
	for id, t := range recs {
		if r, ok := h.req[id]; ok && t < r {
			h.t.Errorf("claim 4 FAIL on m%d: record %x TTL %d < request %d", i, id, t, r)
		}
	}
	return ttls, recs
}

// timeToLive asks member i (a follower forwards to the leader) and checks claim 2.
func (h *harness) timeToLive(i int, id int64) int64 {
	resp, err := h.client(i).TimeToLive(h.ctx, clientv3.LeaseID(id))
	if err != nil {
		h.t.Fatalf("TimeToLive %x via m%d: %v", id, i, err)
	}
	h.t.Logf("claim 2: TimeToLive(%x) via m%d (leader m%d): GrantedTTL %d, TTL %d, request %d",
		id, i, h.leaderIdx(), resp.GrantedTTL, resp.TTL, h.req[id])
	if resp.GrantedTTL < h.req[id] {
		h.t.Errorf("claim 2 FAIL: GrantedTTL %d < request %d", resp.GrantedTTL, h.req[id])
	}
	return resp.GrantedTTL
}

func (h *harness) restartWith(i int, electionTicks int) {
	m := h.clus.Members[i]
	m.Stop(h.t)
	m.ElectionTicks = electionTicks
	if err := m.Restart(h.t); err != nil {
		h.t.Fatal(err)
	}
	h.clus.WaitLeader(h.t)
}

// forceSnapshots writes enough through the leader that it snapshots (SnapshotCount 10) and
// compacts its raft log past a stopped member's index (SnapshotCatchUpEntries 5).
func (h *harness) forceSnapshots(i int) {
	kv := integration.ToGRPC(h.client(i)).KV
	for k := 0; k < 40; k++ {
		if _, err := kv.Put(h.ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte("v")}); err != nil {
			h.t.Fatal(err)
		}
	}
}

func (h *harness) waitRestore(i int, n int) {
	ctx, cancel := context.WithTimeout(h.ctx, 20*time.Second)
	defer cancel()
	if _, err := h.clus.Members[i].LogObserver.Expect(ctx, "restored lease store", n); err != nil {
		h.t.Fatalf("m%d never restored a snapshot's lease store: %v", i, err)
	}
	h.t.Logf("m%d logged \"restored lease store\" %d time(s) (applySnapshot ran lessor.Recover)", i, n)
}

// checkRecover checks claim 1 on member i after a restore: its lessor's ids are exactly the
// bucket's (the image received), each TTL = max(record, own min); ids live before and in the
// records stay live.
func (h *harness) checkRecover(i int, before map[int64]int64) {
	ttls, recs := h.checkMember(i, "after restore:")
	min := minLeaseTTL(h.clus.Members[i])
	for id, r := range recs {
		t, ok := ttls[id]
		if !ok || t != max64(r, min) {
			h.t.Errorf("claim 1 FAIL on m%d: lease %x TTL %d (present %v), want max(record %d, min %d)", i, id, t, ok, r, min)
		}
	}
	for id := range before {
		if _, inRecs := recs[id]; inRecs {
			if _, live := ttls[id]; !live {
				h.t.Errorf("claim 1 FAIL on m%d: %x live before and in records, gone after", i, id)
			}
		}
	}
}

func TestLeaseSnapshotRestore(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size:                   3,
		SnapshotCount:          10,
		SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	h := &harness{t: t, clus: clus, req: map[int64]int64{}, ctx: ctx}

	// Different minLeaseTTL per member (TickMs 10): m0 ElectionTicks 10 -> 1s, m1 2000 -> 30s,
	// m2 6000 -> 90s. Lowest first, so the cluster keeps a quick leader while the others restart.
	h.moveLeader(0)
	h.restartWith(1, 2000)
	h.restartWith(2, 6000)
	h.moveLeader(0)
	for i := range clus.Members {
		t.Logf("m%d: ElectionTicks %d, TickMs %d, minLeaseTTL %d", i, clus.Members[i].ElectionTicks, clus.Members[i].TickMs, minLeaseTTL(clus.Members[i]))
	}

	// Claim 3: through each member, a short and a long request.
	short := map[int]int64{}
	for i := 0; i < 3; i++ {
		short[i] = h.grant(i, 20)
		h.grant(i, 200)
	}
	h.waitApplied([]int{0, 1, 2})
	// Claim 3's lessor side: each member applied every grant at max(request, its own min).
	for i := 0; i < 3; i++ {
		ttls, _ := h.checkMember(i, "after grants:")
		for id, r := range h.req {
			if ttls[id] != max64(r, minLeaseTTL(clus.Members[i])) {
				t.Errorf("claim 3 FAIL: m%d applied %x at %d, want max(%d, %d)", i, id, ttls[id], r, minLeaseTTL(clus.Members[i]))
			}
		}
	}
	a := short[0]
	g0 := h.timeToLive(1, a) // leader m0 answers

	// GrantedTTL differs between members: the leader m2 answers.
	h.moveLeader(2)
	g2 := h.timeToLive(1, a)
	t.Logf("claim 2 (difference across members): GrantedTTL of %x is %d with m0 leading, %d with m2 leading", a, g0, g2)

	// Phase 1: m0 (min 1) lags, restores m2's (min 90) snapshot.
	before0 := lessorTTLs(lessorOf(clus.Members[0].Server))
	clus.Members[0].Stop(t)
	l3 := h.grant(2, 20)
	var big int64
	for id, r := range h.req {
		if r == 200 {
			big = id
			break
		}
	}
	if _, err := h.client(2).Revoke(ctx, clientv3.LeaseID(big)); err != nil {
		t.Fatal(err)
	}
	delete(h.req, big)
	h.forceSnapshots(2)
	h.checkMember(2, "leader m2 after snapshots:")
	if err := clus.Members[0].Restart(t); err != nil {
		t.Fatal(err)
	}
	h.waitRestore(0, 1)
	h.clus.WaitLeader(t)
	h.waitApplied([]int{0, 1, 2})
	h.checkRecover(0, before0)
	after0 := lessorTTLs(lessorOf(clus.Members[0].Server))
	if _, ok := after0[l3]; !ok {
		t.Errorf("m0 lacks %x, granted while it was down", l3)
	}
	if _, ok := after0[big]; ok {
		t.Errorf("m0 still has %x, revoked while it was down", big)
	}
	t.Logf("claim 2 (one member across its restore): m0's lessor TTL of %x: %d before, %d after", a, before0[a], after0[a])
	h.moveLeader(0)
	g0b := h.timeToLive(1, a)
	t.Logf("claim 2 (one member across its restore, through TimeToLive): m0 leading answers GrantedTTL %d before its restore, %d after", g0, g0b)

	// Phase 2: m2 (min 90) lags, restores m0's (min 1) snapshot; records below m2's min.
	l5 := h.grant(0, 30)
	h.waitApplied([]int{0, 1, 2})
	before2 := lessorTTLs(lessorOf(clus.Members[2].Server))
	clus.Members[2].Stop(t)
	l6 := h.grant(0, 30)
	h.forceSnapshots(0)
	h.checkMember(0, "leader m0 after snapshots:")
	if err := clus.Members[2].Restart(t); err != nil {
		t.Fatal(err)
	}
	h.waitRestore(2, 1)
	h.clus.WaitLeader(t)
	h.waitApplied([]int{0, 1, 2})
	h.checkRecover(2, before2)
	after2 := lessorTTLs(lessorOf(clus.Members[2].Server))
	t.Logf("m2 after restore: %x (req 30) TTL %d, %x (req 30, granted while down) TTL %d", l5, after2[l5], l6, after2[l6])

	// Phase 3: m0 lags again, restores m1's (min 30) snapshot. m0's lessor and bucket hold a at
	// 90 (phase 1's image), m1's record of a is 30: a's TTL on m0 goes down, 90 -> 30, still >= 20.
	h.moveLeader(1)
	before0 = lessorTTLs(lessorOf(clus.Members[0].Server))
	clus.Members[0].Stop(t)
	h.forceSnapshots(1)
	h.checkMember(1, "leader m1 after snapshots:")
	if err := clus.Members[0].Restart(t); err != nil {
		t.Fatal(err)
	}
	h.waitRestore(0, 2)
	h.clus.WaitLeader(t)
	h.waitApplied([]int{0, 1, 2})
	h.checkRecover(0, before0)
	after0 = lessorTTLs(lessorOf(clus.Members[0].Server))
	t.Logf("claim 2 (a decrease across one member's restore): m0's lessor TTL of %x: %d before, %d after (request %d)", a, before0[a], after0[a], h.req[a])
	h.moveLeader(0)
	g0c := h.timeToLive(1, a)
	t.Logf("claim 2 (through TimeToLive): m0 leading answers GrantedTTL %d, %d, %d for %x over its two restores", g0, g0b, g0c, a)

	for i := 0; i < 3; i++ {
		h.checkMember(i, "final:")
		for id := range h.req {
			h.timeToLive(i, id)
		}
	}
}

// TestLessorRecoverMinTTL is the lessor-level check of claim 1: lessor B (its own min) recovers
// from lessor A's backend (another min): ids exactly A's records, TTL = max(record, B's min), an
// id live in B before and in the records stays live, one live in B before and not in the
// records is gone.
func TestLessorRecoverMinTTL(t *testing.T) {
	for _, c := range []struct{ minA, minB int64 }{{10, 2}, {2, 10}} {
		lg := zaptest.NewLogger(t)
		beA, _ := betesting.NewDefaultTmpBackend(t)
		defer betesting.Close(t, beA)
		beB, _ := betesting.NewDefaultTmpBackend(t)
		defer betesting.Close(t, beB)
		la := lease.NewLessor(lg, beA, nil, lease.LessorConfig{MinLeaseTTL: c.minA})
		lb := lease.NewLessor(lg, beB, nil, lease.LessorConfig{MinLeaseTTL: c.minB})
		req := map[lease.LeaseID]int64{1: 1, 2: 5, 3: 50}
		for id, ttl := range req {
			if _, err := la.Grant(id, ttl); err != nil {
				t.Fatal(err)
			}
		}
		for _, id := range []lease.LeaseID{1, 4} { // 1: in A's records too; 4: not
			if _, err := lb.Grant(id, req[1]+1); err != nil {
				t.Fatal(err)
			}
		}
		recs := records(beA)
		lb.Recover(beA, nil)
		got := lessorTTLs(lb)
		t.Logf("minA %d minB %d: A's records %v; B after Recover %v", c.minA, c.minB, recs, got)
		if !reflect.DeepEqual(ids(got), ids(recs)) {
			t.Errorf("claim 1 FAIL: recovered ids %v, records %v", ids(got), ids(recs))
		}
		for id, r := range recs {
			if got[id] != max64(r, c.minB) {
				t.Errorf("claim 1 FAIL: %x TTL %d, want max(%d, %d)", id, got[id], r, c.minB)
			}
			if got[id] < req[lease.LeaseID(id)] {
				t.Errorf("claim 2 FAIL: %x TTL %d < request %d", id, got[id], req[lease.LeaseID(id)])
			}
		}
		la.Stop()
		lb.Stop()
	}
}
