package snaprepair

import (
	"bytes"
	"context"
	"fmt"
	"github.com/Masterminds/semver/v3"
	srvversion "go.etcd.io/etcd/server/v3/etcdserver/version"
	"io"
	"math"
	"net"
	"strings"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3/raftpb"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

func mustPanic(t *testing.T, name string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("%s: no panic", name)
		}
		t.Logf("%s: the OLD counterexample still panics in Go: %v", name, r)
	}()
	f()
}

// ---- (a) the counterexamples violate the NEW premises ----

// S1 NilReader: NewMessage(&Message{}, nil, 0) has no close contract (rc nil).
func TestS1NilReader(t *testing.T) {
	v := NewMessagePremises(&raftpb.Message{}, nil, 0, CapOf(nil))
	if len(v) == 0 {
		t.Fatal("NilReader satisfies the NEW premises")
	}
	t.Logf("NilReader violates: %q", v)
	mustPanic(t, "NilReader", func() {
		m := snap.NewMessage(&raftpb.Message{}, nil, 0)
		m.CloseWithError(nil)
	})
}

// S1 HandOver: the pipe's reader wrapped before T is given up: no close contract.
func TestS1HandOver(t *testing.T) {
	g := NewGhostPipe()
	v := NewMessagePremises(&raftpb.Message{}, g.PR, 0, nil)
	if len(v) == 0 {
		t.Fatal("HandOver satisfies the NEW premises")
	}
	t.Logf("HandOver violates: %q", v)
	// the Go run: the message closes pr, the writer's Write returns, CloseWithError would hand T back
	m := snap.NewMessage(&raftpb.Message{}, g.PR, 0)
	m.CloseWithError(nil)
	var w io.Writer = g.PW
	n, err := w.Write([]byte{1})
	g.PW.CloseWithError(nil)
	if g.handed || err == nil {
		t.Fatalf("unexpected: handed %v, Write %d %v", g.handed, n, err)
	}
	t.Logf("HandOver: Write returned (%d, %v) though T was never given up (handed=%v): the OLD "+
		"CloseWithError hands back a T nobody gave up", n, err, g.handed)
	// the same after GiveUpT: the premise holds
	g2 := NewGhostPipe()
	rc, cap := g2.GiveUpT()
	if v := NewMessagePremises(&raftpb.Message{}, rc, 0, cap); len(v) != 0 {
		t.Fatalf("after the hand-over the premises fail: %q", v)
	}
	g2.PW.CloseWithError(nil)
}

// S2 NegativeSize (sz = -1) and its overflow variant (sz = MaxInt64 with a non-empty rs).
func TestS2NegativeSize(t *testing.T) {
	v := NewMessagePremises(&raftpb.Message{}, nil, -1, nil)
	found := false
	for _, s := range v {
		found = found || strings.HasPrefix(s, "0 <= sz")
	}
	if !found {
		t.Fatalf("sz = -1 satisfies the size premise: %q", v)
	}
	t.Logf("NegativeSize violates: %q", v)
	mustPanic(t, "NegativeSize", func() {
		m := snap.NewMessage(&raftpb.Message{}, nil, -1)
		if m.TotalSize < 0 {
			panic(fmt.Sprintf("TotalSize = %d < 0", m.TotalSize))
		}
	})
	to := uint64(7)
	rs := &raftpb.Message{To: &to}
	g := NewGhostPipe()
	rc, cap := g.GiveUpT()
	v = NewMessagePremises(rs, rc, math.MaxInt64, cap)
	if len(v) == 0 {
		t.Fatal("overflow variant satisfies the premises")
	}
	t.Logf("Overflow (sz = MaxInt64, proto.Size(rs) = 2) violates: %q", v)
	m := snap.NewMessage(rs, rc, math.MaxInt64)
	if m.TotalSize >= 0 {
		t.Fatalf("expected an overflow, TotalSize = %d", m.TotalSize)
	}
	t.Logf("Overflow: Go's TotalSize = %d", m.TotalSize)
	g.PW.CloseWithError(nil)
}

// S3 Scratch: the exact-size wrapper reads a byte into p, returns (0, ErrExpectEOF); MultiReader
// passes it on. The OLD clause (p unchanged past n) fails; the NEW one (len(p) bytes, the first n
// the stream's) holds. The premises of S1/S2 hold for this program (T given up first, sz = 0).
func TestS3Scratch(t *testing.T) {
	g := NewGhostPipe()
	go func() {
		var w io.Writer = g.PW
		w.Write([]byte{7})
	}()
	rc, cap := g.GiveUpT()
	if v := NewMessagePremises(&raftpb.Message{}, rc, 0, cap); len(v) != 0 {
		t.Fatalf("Scratch violates S1/S2: %q", v)
	}
	m := snap.NewMessage(&raftpb.Message{}, rc, 0)
	var b bytes.Buffer
	mr := io.MultiReader(&b, m.ReadCloser)
	p := make([]byte, 1)
	n, err := mr.Read(p)
	oldOK := n > 0 || p[0] == 0
	newOK := n >= 0 && n <= len(p) && len(p) == 1
	t.Logf("Scratch: Read = (%d, %v), p = %v: OLD clause %v, NEW clause %v", n, err, p, oldOK, newOK)
	if oldOK || !newOK {
		t.Fatal("expected the OLD clause to fail and the NEW one to hold")
	}
}

// ---- (b) the NEW premises hold on etcd's own paths ----

func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return l.Addr().String()
}

func waitVersion(t *testing.T, s *etcdserver.EtcdServer) {
	for i := 0; i < 200; i++ {
		if v := s.ClusterVersion(); v != nil {
			return
		}
		time.Sleep(50 * time.Millisecond)
	}
	t.Fatal("no cluster version after 10s")
}

// checkVersion checks S4's premise of one member: the cluster version stored in its backend's
// `cluster` bucket parses (semverValid), is Major.Minor.0, not above the binary's major.minor
// (semverAtMostServer: MustDetectDowngrade's test), and no downgrade is enabled.
func checkVersion(t *testing.T, name string, s *etcdserver.EtcdServer) {
	mb := schema.NewMembershipBackend(zap.NewNop(), s.Backend())
	cv := mb.ClusterVersionFromBackend()
	if cv == nil {
		t.Fatalf("%s: no cluster version in the backend", name)
	}
	var smaj, smin uint64
	if _, err := fmt.Sscanf(version.Version, "%d.%d.", &smaj, &smin); err != nil {
		t.Fatal(err)
	}
	if cv.Patch() != 0 || cv.Prerelease() != "" || cv.Metadata() != "" {
		t.Errorf("%s: stored cluster version %v is not Major.Minor.0", name, cv)
	}
	if cv.Major() > smaj || (cv.Major() == smaj && cv.Minor() > smin) {
		t.Errorf("%s: stored cluster version %v above the server's %d.%d.0 (MustDetectDowngrade panics)", name, cv, smaj, smin)
	}
	if d := mb.DowngradeInfoFromBackend(); d != nil && d.Enabled {
		t.Errorf("%s: a downgrade is enabled: %+v", name, d)
	}
	t.Logf("%s: stored cluster version %v, in memory %v, server %s (cut %d.%d.0): ok", name, cv,
		s.ClusterVersion(), version.Version, smaj, smin)
}

// S1/S2/S3 on a live one-member server's backend (etcd's merged-snapshot path, replayed), and
// S4 on what the server stores.
func TestRealPathOneMember(t *testing.T) {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	caddr := freeAddr(t)
	s, err := etcdstart.StartServer("snapr1", freeAddr(t), caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	defer s.Stop()
	if err := etcdstart.Serve(s, caddr); err != nil {
		t.Fatal(err)
	}
	<-s.ReadyNotify()
	waitVersion(t, s)
	checkVersion(t, "snapr1", s)
	cli, err := etcdstart.NewClient(caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	runs, scratch := 0, 0
	for round := 0; round < 4; round++ {
		for i := 0; i < 200; i++ {
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			_, err := cli.Put(ctx, fmt.Sprintf("k%d-%d", round, i), strings.Repeat("v", 100*round+1))
			cancel()
			if err != nil {
				t.Fatal(err)
			}
		}
		s.KV().Commit()
		for _, bs := range []int{1, 7, 512, 4096, 32 * 1024, 1 << 20} {
			for _, early := range []bool{false, true} {
				r := RunMerged(lg, s.Backend(), bs, early)
				runs++
				scratch += r.Body.OldViolations
				if len(r.Violations) != 0 || r.Body.NewViolations != 0 || !r.CloseOK {
					t.Errorf("round %d bs %d early %v: violations %q, new-clause failures %d, close ok %v",
						round, bs, early, r.Violations, r.Body.NewViolations, r.CloseOK)
				}
				if bs == 4096 && !early {
					t.Logf("round %d: Size %d, proto.Size %d, TotalSize %d, %d reads, WriteTo %d bytes",
						round, r.Size, r.ProtoSize, r.TotalSize, r.Body.Reads, r.WriterBytes)
				}
			}
		}
	}
	t.Logf("%d merged runs: NEW premises held in all; reads that wrote past n (OLD clause) %d", runs, scratch)
}

// capture is a zap core recording the merged-snapshot path's log lines with their fields.
type capture struct {
	mu   *sync.Mutex
	recs *[]string
	vals map[string]*[]int64
}

func (c capture) Enabled(zapcore.Level) bool        { return true }
func (c capture) With([]zapcore.Field) zapcore.Core { return c }
func (c capture) Sync() error                       { return nil }
func (c capture) Check(e zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	return ce.AddCore(e, c)
}
func (c capture) Write(e zapcore.Entry, fs []zapcore.Field) error {
	keys := []string{"sending database snapshot", "sent database snapshot", "sent database snapshot to writer",
		"received and saved database snapshot", "applied snapshot", "failed to send database snapshot"}
	for _, k := range keys {
		if e.Message == k || (k == "applied snapshot" && strings.Contains(e.Message, k)) {
			c.mu.Lock()
			for _, f := range fs {
				if f.Key == "bytes" {
					*c.vals[k] = append(*c.vals[k], f.Integer)
				}
			}
			*c.recs = append(*c.recs, k)
			c.mu.Unlock()
		}
	}
	return nil
}

// A three-member cluster whose third member starts after the others compacted raft's log (SnapCount
// 1, SnapCatchUp 1, as examples/etcd/partition): the leader sends it a merged snapshot through
// etcd's own createMergedSnapshotMessage, snapshotSender and SaveDBFrom. The sizes it logs are
// TotalSize (the sender) and WriteTo's count (the pipe's writer); S4 on all three members, the
// third's cluster bucket restored from the snapshot (Recover's path).
func TestRealPathSnapshotSend(t *testing.T) {
	t.Chdir(t.TempDir())
	c := capture{mu: &sync.Mutex{}, recs: &[]string{}, vals: map[string]*[]int64{}}
	for _, k := range []string{"sending database snapshot", "sent database snapshot", "sent database snapshot to writer",
		"received and saved database snapshot", "applied snapshot", "failed to send database snapshot"} {
		c.vals[k] = &[]int64{}
	}
	lg := zap.New(c)
	names := []string{"snapr-a", "snapr-b", "snapr-c"}
	var peers [3]string
	var clients [3]string
	m := types.URLsMap{}
	for i := range names {
		peers[i], clients[i] = freeAddr(t), freeAddr(t)
		m[names[i]] = types.URLs{{Scheme: "http", Host: peers[i]}}
	}
	var srvs [3]*etcdserver.EtcdServer
	start := func(i int) {
		s, err := etcdstart.NewMember(names[i], m[names[i]], peers[i], clients[i], m, "snapr", 1, 1, lg)
		if err != nil {
			t.Fatal(err)
		}
		s.Start()
		if err := etcdstart.Serve(s, clients[i]); err != nil {
			t.Fatal(err)
		}
		srvs[i] = s
	}
	start(0)
	start(1)
	defer func() {
		for _, s := range srvs {
			if s != nil {
				s.Stop()
			}
		}
	}()
	<-srvs[0].ReadyNotify()
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clients[0], clients[1]}, Logger: zap.NewNop(),
		DialTimeout: 2 * time.Second})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	for i := 0; i < 300; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		_, err := cli.Put(ctx, fmt.Sprintf("k%d", i), strings.Repeat("x", 200))
		cancel()
		if err != nil {
			t.Fatal(err)
		}
	}
	start(2)
	deadline := time.Now().Add(30 * time.Second)
	for time.Now().Before(deadline) {
		c.mu.Lock()
		n := len(*c.vals["applied snapshot"]) + countRec(*c.recs, "applied snapshot")
		c.mu.Unlock()
		if n > 0 {
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	time.Sleep(time.Second)
	c.mu.Lock()
	sending := append([]int64(nil), *c.vals["sending database snapshot"]...)
	writer := append([]int64(nil), *c.vals["sent database snapshot to writer"]...)
	saved := append([]int64(nil), *c.vals["received and saved database snapshot"]...)
	nApplied := countRec(*c.recs, "applied snapshot")
	nFail := countRec(*c.recs, "failed to send database snapshot")
	c.mu.Unlock()
	t.Logf("merged snapshots: sending (TotalSize as uint64) %v; WriteTo counts %v; saved %v; applied %d; failed sends %d",
		sending, writer, saved, nApplied, nFail)
	if len(sending) == 0 {
		t.Fatal("no merged snapshot was sent")
	}
	for _, b := range sending {
		// the field is uint64(TotalSize): a negative TotalSize would log as >= 2^63
		if uint64(b) >= 1<<48+1<<20 {
			t.Errorf("TotalSize %d out of the premise's range", uint64(b))
		}
	}
	for _, b := range writer {
		if b < 0 || b >= SizeBound {
			t.Errorf("WriteTo count (the snapshot's Size) %d out of [0, 2^48)", b)
		}
	}
	for i, s := range srvs {
		waitVersion(t, s)
		checkVersion(t, names[i], s)
	}
}

func countRec(recs []string, k string) int {
	n := 0
	for _, r := range recs {
		if r == k {
			n++
		}
	}
	return n
}

// verPremise is S4's premise of one ClusterVersionSet value v (semverValid: semver.MustParse
// accepts it; semverAtMostServer: not above the server's Major.Minor.0).
func verPremise(v string) bool {
	cv, err := semver.NewVersion(v)
	if err != nil {
		return false
	}
	sv := semver.MustParse(version.Version)
	cut := semver.New(sv.Major(), sv.Minor(), 0, "", "")
	return !cut.LessThan(cv)
}

// S4 (a): attack 8's forged versions (99.0.0, 3.8.1) violate the premise, and are exactly the
// ones Recover's MustDetectDowngrade panics on; what the monitor proposes (Major.Minor.0 of the
// members' minimum, or 3.0.0) satisfies it.
func TestS4ForgedVersion(t *testing.T) {
	sv := semver.MustParse(version.Version)
	for _, v := range []string{"99.0.0", "3.8.1", "3.9.0", "3.8.0", "3.7.0", "3.0.0"} {
		ok := verPremise(v)
		panicked := func() (p bool) {
			defer func() { p = recover() != nil }()
			srvversion.MustDetectDowngrade(zap.NewNop(), sv, semver.MustParse(v))
			return false
		}()
		t.Logf("ClusterVersionSet %s: premise %v, MustDetectDowngrade panics %v", v, ok, panicked)
		if ok == panicked {
			t.Errorf("%s: the premise (%v) does not match MustDetectDowngrade (panics %v)", v, ok, panicked)
		}
	}
}
