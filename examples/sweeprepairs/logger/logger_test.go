package logger

import (
	"context"
	"errors"
	"fmt"
	"net"
	"os"
	"reflect"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"

	"github.com/Masterminds/semver/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// mustPanic runs f and fails unless it panics; returns the panic value.
func mustPanic(t *testing.T, name string, f func()) any {
	t.Helper()
	r := Safe(f)
	if r == nil {
		t.Fatalf("%s: did not panic", name)
	}
	t.Logf("%s panicked: %T: %v", name, r, r)
	return r
}

// mustFail asserts that a premise's Go meaning fails (the counterexample is excluded).
func mustFail(t *testing.T, name string, err error) {
	t.Helper()
	if err == nil {
		t.Fatalf("%s: premise holds, expected it to fail", name)
	}
	t.Logf("%s: premise fails: %v", name, err)
}

func mustHold(t *testing.T, name string, err error) {
	t.Helper()
	if err != nil {
		t.Fatalf("%s: premise fails: %v", name, err)
	}
	t.Logf("%s: premise holds", name)
}

// ---- (a) the counterexamples against the new premises ----

// TestA0QuotaZero runs first (quotaLogOnce is per process; the cluster test below consumes it):
// storage.NewBackendQuota (no premise on lg) panics at a zero logger on the first call (family #5).
func TestA0QuotaZero(t *testing.T) {
	zl := &zap.Logger{}
	mustFail(t, "zapLoggerOk(&zap.Logger{}) [NewBackendQuota]", ZapLoggerOk(zl))
	mustPanic(t, "NewBackendQuota(&zap.Logger{}, 1<<20, nil, q)", func() {
		storage.NewBackendQuota(zl, 1<<20, nil, "q")
	})
}

// TestA1ZapZero: zap-zero.md's programs; zapLoggerOk fails for each zero logger.
func TestA1ZapZero(t *testing.T) {
	for _, mk := range []struct {
		name string
		l    func() *zap.Logger
	}{{"&zap.Logger{}", func() *zap.Logger { return &zap.Logger{} }},
		{"new(zap.Logger)", func() *zap.Logger { return new(zap.Logger) }}} {
		mustFail(t, "zapLoggerOk("+mk.name+")", ZapLoggerOk(mk.l()))
		mustPanic(t, mk.name+".Debug", func() { mk.l().Debug("x") })
		mustPanic(t, mk.name+".Info", func() { mk.l().Info("x") })
		mustPanic(t, mk.name+".Warn", func() { mk.l().Warn("x") })
		mustPanic(t, mk.name+".Error", func() { mk.l().Error("x") })
		mustPanic(t, mk.name+".Check", func() { _ = mk.l().Check(zapcore.WarnLevel, "x") })
		mustPanic(t, mk.name+".Fatal", func() { mk.l().Fatal("x") })
		// Panic: the spec's post says the panic value is the message; Go's is a runtime error
		// (observable with recover, which GooseLang has: with_defer_recover).
		r := mustPanic(t, mk.name+".Panic", func() { mk.l().Panic("x") })
		if r == "x" {
			t.Fatalf("zero logger's Panic panicked with the message")
		}
	}
	// Other zap options that the constructors accept but zapLoggerOk excludes.
	mustFail(t, "zapLoggerOk(WithClock(nil))", ZapLoggerOk(zap.NewNop().WithOptions(zap.WithClock(nil))))
	mustFail(t, "zapLoggerOk(WithFatalHook(WriteThenPanic))",
		ZapLoggerOk(zap.NewNop().WithOptions(zap.WithFatalHook(zapcore.WriteThenPanic))))
	mustFail(t, "zapLoggerOk(Hooks(...))",
		ZapLoggerOk(zap.NewExample(zap.Hooks(func(zapcore.Entry) error { panic("hook") }))))
}

type badWS struct{}

func (badWS) Write(p []byte) (int, error) { panic("badWS.Write") }
func (badWS) Sync() error                  { return nil }

// TestA2CheckedEntry: zap-zero.md's double Write of a hand-built entry; zapEntry fails for it,
// and for a second Write of an entry Check returned.
func TestA2CheckedEntry(t *testing.T) {
	ce := &zapcore.CheckedEntry{ErrorOutput: badWS{}}
	mustFail(t, "zapEntry(hand-built ce)", ZapEntryConsume(ce))
	mustPanic(t, "hand-built ce: Write twice", func() { ce.Write(); ce.Write() })

	l := zap.NewExample() // Debug enabled: Check returns an entry
	ce2 := CheckTracked(l, zapcore.InfoLevel, "x")
	if ce2 == nil {
		t.Fatal("Check returned nil")
	}
	mustHold(t, "zapEntry(ce from Check), first Write", ZapEntryConsume(ce2))
	ce2.Write()
	mustFail(t, "zapEntry(ce from Check), second Write", ZapEntryConsume(ce2))
	if ce3 := CheckTracked(zap.NewNop(), zapcore.InfoLevel, "x"); ce3 != nil {
		t.Fatal("nop logger's Check returned an entry")
	}
}

type noCluster struct{}

func (noCluster) Version() *semver.Version { return nil }

type str string

func (s str) String() string { return string(s) }

// TestA3Family: the logger family's counterexamples (logger-family.md #3, #14, #15, #9-11,
// lessor-methods.md) and L4 (raft's zap logger), each with a zero logger that zapLoggerOk excludes.
func TestA3Family(t *testing.T) {
	zl := &zap.Logger{}
	mustFail(t, "zapLoggerOk(&zap.Logger{}) [family]", ZapLoggerOk(zl))

	// #3 txn.WarnOfFailedRequest: unconditional lg.Warn.
	mustPanic(t, "txn.WarnOfFailedRequest(&zap.Logger{})", func() {
		txn.WarnOfFailedRequest(zl, time.Now(), str("req"), &pb.RangeResponse{}, errors.New("e"))
	})
	// #14 mvcc.hashStorage.Store: unconditional s.lg.Info.
	mustPanic(t, "mvcc.NewHashStorage(&zap.Logger{}).Store", func() {
		mvcc.NewHashStorage(zl, nil).Store(mvcc.KeyValueHash{})
	})
	// #15 traceutil: EnsureTrace with the zero logger, then LogWithStepThreshold.
	mustPanic(t, "traceutil.EnsureTrace(&zap.Logger{}).LogWithStepThreshold", func() {
		_, tr := traceutil.EnsureTrace(context.Background(), zl, "op")
		tr.LogWithStepThreshold(0)
	})
	// a nil trace logger is fine (TODO/Get's traces): ownTrace's `lg = null ∨ zapLoggerOk lg`
	if r := Safe(func() {
		_, tr := traceutil.EnsureTrace(context.Background(), nil, "op")
		tr.LogWithStepThreshold(0)
	}); r != nil {
		t.Fatalf("nil trace logger panicked: %v", r)
	}
	// L2b (#9-11): NewLessor's lessor with the zero logger, Promote then Grant (lessor-methods.md).
	dir := t.TempDir()
	be := backend.NewDefaultBackend(zap.NewNop(), dir+"/db")
	defer be.Close()
	le := lease.NewLessor(zl, be, noCluster{}, lease.LessorConfig{})
	le.SetCheckpointer(func(context.Context, *pb.LeaseCheckpointRequest) error { return nil })
	le.Promote(0)
	mustPanic(t, "lessor(&zap.Logger{}).Promote; Grant(1, 1000)", func() { _, _ = le.Grant(1, 1000) })
	// L4: raft's zap logger over a zero logger; NewRaftLoggerZap's own body does not panic
	// (WithOptions/Sugar only clone), its first log does.
	rl := etcdserver.NewRaftLoggerZap(zl)
	mustPanic(t, "NewRaftLoggerZap(&zap.Logger{}).Infof", func() { rl.Infof("x %d", 1) })
	mustFail(t, "zapLoggerOk(NewRaftLoggerZap(&zap.Logger{}).lg)", ZapLoggerOk(raftZapLg(rl)))
}

// raftZapLg reads a *etcdserver.zapRaftLogger's lg.
func raftZapLg(rl any) *zap.Logger {
	v := reflect.ValueOf(rl).Elem()
	return field(v, "lg").Interface().(*zap.Logger)
}

// SrvLoggerOk is L3's s-premise, its logger part (srvLoggerOk s: s.lg holds a zapLoggerOk
// logger) with the lock Logger() reads it under (s.lgMu, which every server predicate's
// srvLgReader names).
func SrvLoggerOk(s *etcdserver.EtcdServer) error {
	v := reflect.ValueOf(s).Elem()
	if field(v, "lgMu").IsNil() {
		return fmt.Errorf("nil lgMu")
	}
	return ZapLoggerOk(field(v, "lg").Interface().(*zap.Logger))
}

// SrvReqFieldsOk is the part of isServerReqM adjustTicks reads: the cluster, the raft node and the
// transport set (non-nil), Cfg's ticks positive.
func SrvReqFieldsOk(s *etcdserver.EtcdServer) error {
	v := reflect.ValueOf(s).Elem()
	if field(v, "cluster").IsNil() {
		return fmt.Errorf("nil cluster")
	}
	r := field(v, "r")
	nc := field(r, "raftNodeConfig")
	if field(nc, "Node").IsNil() {
		return fmt.Errorf("nil raft Node")
	}
	if field(nc, "transport").IsNil() {
		return fmt.Errorf("nil transport")
	}
	return nil
}

// TestA4ZeroServer: L3, &EtcdServer{} (adjustTicks and purgeFile's refutation: s.Logger() on a nil
// lgMu) fails the s-premise.
func TestA4ZeroServer(t *testing.T) {
	s := &etcdserver.EtcdServer{}
	mustFail(t, "srvLoggerOk(&EtcdServer{})", SrvLoggerOk(s))
	mustFail(t, "isServerReqM fields(&EtcdServer{})", SrvReqFieldsOk(s))
	mustPanic(t, "(&EtcdServer{}).Logger() [adjustTicks/purgeFile's first line]", func() { s.Logger() })
}

// ---- (b) the premises over the real uses ----

// TestB1Constructors: the loggers zap's constructors and etcd's derivations build pass, and their
// logging methods return (Debug..Error, Check+Write once, Panic with the message).
func TestB1Constructors(t *testing.T) {
	prod, _ := zap.NewProduction()
	dev, _ := zap.NewDevelopment()
	nop := zap.NewNop()
	cases := map[string]*zap.Logger{
		"zap.NewNop()":                               nop,
		"zap.NewNop().Named(raft)":                   nop.Named("raft"),
		"zap.NewNop().WithOptions(AddCallerSkip(1))": nop.WithOptions(zap.AddCallerSkip(1)),
		"zap.NewNop().With(field)":                   nop.With(zap.String("k", "v")),
		"raft's NewRaftLoggerZap(NewNop().Named(raft)).lg": raftZapLg(
			etcdserver.NewRaftLoggerZap(nop.Named("raft"))),
		"zap.NewExample()":                  zap.NewExample(),
		"zap.NewProduction() [no Lean spec]":  prod,
		"zap.NewDevelopment() [no Lean spec]": dev,
	}
	for name, l := range cases {
		mustHold(t, "zapLoggerOk("+name+")", ZapLoggerOk(l))
		if strings.Contains(name, "NewProduction") || strings.Contains(name, "NewDevelopment") ||
			strings.Contains(name, "Example") {
			continue // they print; behavior checked on the nop ones
		}
		if r := Safe(func() {
			l.Debug("x")
			l.Info("x")
			l.Warn("x")
			l.Error("x")
			if ce := CheckTracked(l, zapcore.WarnLevel, "x"); ce != nil {
				if err := ZapEntryConsume(ce); err != nil {
					panic(err)
				}
				ce.Write()
			}
		}); r != nil {
			t.Fatalf("%s: a logging method panicked: %v", name, r)
		}
		if r := Safe(func() { l.Panic("msg") }); r != "msg" {
			t.Fatalf("%s: Panic's value %v, not the message", name, r)
		}
	}
	rl := etcdserver.NewRaftLoggerZap(nop)
	if r := Safe(func() { rl.Infof("x %d", 1); rl.Warningf("y"); rl.Debugf("z") }); r != nil {
		t.Fatalf("NewRaftLoggerZap(NewNop()): %v", r)
	}
}

func freePorts(t *testing.T, n int) []string {
	var ls []net.Listener
	var out []string
	for i := 0; i < n; i++ {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		ls = append(ls, l)
		out = append(out, l.Addr().String())
	}
	for _, l := range ls {
		l.Close()
	}
	return out
}

// checkAll walks root's loggers and checks zapLoggerOk of every non-nil one.
func checkAll(t *testing.T, name string, root any) int {
	t.Helper()
	fs := Loggers(root)
	ok := 0
	seen := map[*zap.Logger]bool{}
	for _, f := range fs {
		if err := ZapLoggerOk(f.L); err != nil {
			t.Errorf("%s: %s: %v", name, f.Path, err)
			continue
		}
		ok++
		seen[f.L] = true
	}
	t.Logf("%s: %d *zap.Logger references reachable (%d distinct), every one zapLoggerOk", name, ok, len(seen))
	for i, f := range fs {
		_ = i
		t.Logf("  at %s", f.Path)
	}
	return ok
}

// TestB2Cluster: the examples' construction paths (cluster3.StartCluster over etcdstart's
// newServer and NewServer, cluster3.NewClient over clientv3.New, with zap.NewNop() as every example
// passes): after a Put and a Get, the servers are stopped and every *zap.Logger reachable from each
// server (its lg, the lessor's, the auth store's, the backend's and bbolt's, the cluster's, the
// snapshotter's, the transport's and its peers', raft's zapRaftLogger, the hash storage's, ...) and
// from the client is zapLoggerOk; each server meets srvLoggerOk and the isServerReqM fields.
func TestB2Cluster(t *testing.T) {
	dir := t.TempDir()
	wd, _ := os.Getwd()
	if err := os.Chdir(dir); err != nil {
		t.Fatal(err)
	}
	defer os.Chdir(wd)
	p := freePorts(t, 9)
	cfg := cluster3.Config{Token: "lgchk", Name1: "lgchk-1", Name2: "lgchk-2", Name3: "lgchk-3",
		Peer1: p[0], Peer2: p[1], Peer3: p[2], Client1: p[3], Client2: p[4], Client3: p[5],
		Bridge1: p[6], Bridge2: p[7], Bridge3: p[8], SnapCount: etcdstart.NoSnapCount,
		SnapCatchUp: etcdstart.NoSnapCatchUp}
	lg := zap.NewNop()
	mustHold(t, "zapLoggerOk(lg = zap.NewNop()) [the examples' cfg.Logger]", ZapLoggerOk(lg))
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		t.Fatal("StartCluster failed")
	}
	cli, err := cluster3.NewClient(cfg, lg)
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	if _, err := cli.Put(ctx, "k", "v"); err != nil {
		t.Fatal(err)
	}
	if _, err := cli.Get(ctx, "k"); err != nil {
		t.Fatal(err)
	}
	cancel()
	for i, s := range srvs {
		mustHold(t, fmt.Sprintf("srvLoggerOk(member %d)", i+1), SrvLoggerOk(s))
		mustHold(t, fmt.Sprintf("isServerReqM fields(member %d)", i+1), SrvReqFieldsOk(s))
		if s.Logger() != lg {
			t.Fatalf("member %d: s.Logger() is not cfg.Logger", i+1)
		}
	}
	mustHold(t, "zapLoggerOk(cli.GetLogger())", ZapLoggerOk(cli.GetLogger()))
	cli.Close()
	for _, s := range srvs {
		s.Stop()
	}
	for _, b := range brs {
		b.Close()
	}
	total := 0
	for i, s := range srvs {
		total += checkAll(t, fmt.Sprintf("member %d", i+1), s)
	}
	total += checkAll(t, "client", cli)
	if total == 0 {
		t.Fatal("no logger found")
	}
}
