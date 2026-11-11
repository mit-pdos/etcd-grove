package zaplogger

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"net"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"runtime"
	"runtime/debug"
	"strings"
	"sync"
	"testing"
	"time"
	"unsafe"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// ---- helpers ----

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

// mustReturn runs f and fails if it panics.
func mustReturn(t *testing.T, name string, f func()) {
	t.Helper()
	if r := Safe(f); r != nil {
		t.Fatalf("%s: panicked: %v", name, r)
	}
	t.Logf("%s returned", name)
}

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

// ---- child processes ----
//
// A run that exits the process (Fatal), panics in a goroutine of the library's (OpenBackend), or
// consumes per-process state (NewBackendQuota's quotaLogOnce) runs in a child: the test binary
// re-executed with -test.run=^<the test>$ and childEnv naming the mode; the test, seeing childEnv,
// runs the mode instead of its body.

const childEnv = "ZAPLOGGER_CHILD_MODE"

const childReturned = "ZAPLOGGER-CHILD-RETURNED"

// childModes: what a child runs. A mode that returns makes the child print childReturned and
// exit 0.
var childModes = map[string]func(){
	"fatal-nop": func() { zap.NewNop().Fatal("fatal") },

	"quota-zero-neg": func() { storage.NewBackendQuota(&zap.Logger{}, -1, nil, "q") },
	"quota-zero-pos": func() { storage.NewBackendQuota(&zap.Logger{}, 1<<20, nil, "q") },
	"quota-nop-neg":  func() { storage.NewBackendQuota(zap.NewNop(), -1, nil, "q") },
	"quota-nop-pos":  func() { storage.NewBackendQuota(zap.NewNop(), 1<<20, nil, "q") },
	"quota-nil-neg":  func() { storage.NewBackendQuota(nil, -1, nil, "q") },
	"quota-nil-pos":  func() { storage.NewBackendQuota(nil, 1<<20, nil, "q") },

	"openbackend-zero": func() { storage.OpenBackend(srvCfg(&zap.Logger{}, os.Getenv("ZAPLOGGER_DIR")), nil) },

	"clientv3-zero": func() {
		cli, err := clientv3.New(clientv3.Config{Logger: &zap.Logger{},
			Endpoints: []string{os.Getenv("ZAPLOGGER_ENDPOINT")}})
		if err != nil {
			panic(fmt.Sprintf("clientv3.New: %v", err))
		}
		fmt.Println("ZAPLOGGER-CLIENT-NEW-RETURNED")
		rangeNoWait(cli, time.Second)
	},
}

// childMain runs the mode named by childEnv, if any (in a child); otherwise returns.
func childMain() {
	m := os.Getenv(childEnv)
	if m == "" {
		return
	}
	f, ok := childModes[m]
	if !ok {
		fmt.Println("unknown child mode", m)
		os.Exit(3)
	}
	f()
	fmt.Println(childReturned)
	os.Exit(0)
}

// runChild runs mode in a child process under test (a top-level test name); returns its exit code
// and output.
func runChild(t *testing.T, test, mode string, env ...string) (int, string) {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run=^"+test+"$", "-test.count=1", "-test.v")
	cmd.Env = append(append(os.Environ(), childEnv+"="+mode), env...)
	out, err := cmd.CombinedOutput()
	code := 0
	if err != nil {
		var ee *exec.ExitError
		if !errors.As(err, &ee) {
			t.Fatalf("child %s: %v", mode, err)
		}
		code = ee.ExitCode()
	}
	return code, string(out)
}

// childPanics asserts that mode's child dies of a panic (exit 2, "panic:" in its output, never
// childReturned), and that the output contains each of want.
func childPanics(t *testing.T, test, mode string, want []string, env ...string) {
	t.Helper()
	code, out := runChild(t, test, mode, env...)
	if code == 0 || strings.Contains(out, childReturned) || !strings.Contains(out, "panic:") {
		t.Fatalf("child %s: exit %d, expected a panic; output:\n%s", mode, code, out)
	}
	for _, w := range want {
		if !strings.Contains(out, w) {
			t.Fatalf("child %s: output lacks %q:\n%s", mode, w, out)
		}
	}
	t.Logf("child %s: exit %d, panicked (%s)", mode, code, firstLine(out, "panic:"))
}

// childReturns asserts that mode's child returned (exit 0, childReturned printed).
func childReturns(t *testing.T, test, mode string, env ...string) {
	t.Helper()
	code, out := runChild(t, test, mode, env...)
	if code != 0 || !strings.Contains(out, childReturned) {
		t.Fatalf("child %s: exit %d, expected it to return; output:\n%s", mode, code, out)
	}
	t.Logf("child %s: returned", mode)
}

func firstLine(out, prefix string) string {
	for _, l := range strings.Split(out, "\n") {
		if strings.HasPrefix(l, prefix) {
			return l
		}
	}
	return ""
}

// ---- 1. the zero logger ----

// TestZeroLoggerPanics backs the premise zapLoggerOk l of zap's trusted specs
// (Spec/go_uber_org/zap/Logger__{Debug,Info,Warn,Error,Fatal,Check}.lean): on a zero logger
// (&zap.Logger{}, new(zap.Logger)), which zapLoggerOk excludes, each of them panics. Fatal panics
// too, at log.clock.Now() in (*Logger).check (a nil clock), before it can write or exit.
func TestZeroLoggerPanics(t *testing.T) {
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
		mustPanic(t, mk.name+".Check(WarnLevel)", func() { _ = mk.l().Check(zapcore.WarnLevel, "x") })

		// Fatal: a nil-pointer runtime panic in (*Logger).check (at log.clock.Now(): Fatal skips
		// the core.Enabled shortcut, so the first nil it touches is the clock), not an exit.
		var stack string
		r := Safe(func() {
			defer func() {
				if r := recover(); r != nil {
					stack = string(debug.Stack())
					panic(r)
				}
			}()
			mk.l().Fatal("x")
		})
		if r == nil {
			t.Fatalf("%s.Fatal: did not panic", mk.name)
		}
		if _, ok := r.(runtime.Error); !ok {
			t.Fatalf("%s.Fatal: panic %T %v, not a runtime error", mk.name, r, r)
		}
		if !strings.Contains(stack, "zap.(*Logger).check") {
			t.Fatalf("%s.Fatal: panic not in (*Logger).check:\n%s", mk.name, stack)
		}
		t.Logf("%s.Fatal panicked in (*Logger).check (nil clock): %v", mk.name, r)
	}
}

// ---- 2. the constructors ----

// TestConstructorsOk backs zap's constructor specs (Spec/go_uber_org/zap/NewNop.lean: the result is
// zapLoggerOk) and the use of the logging specs on them: zap.NewNop(), NewExample(),
// NewProduction(), NewDevelopment() and the derivations Named/With/WithOptions(AddCallerSkip(1))
// of NewNop() satisfy ZapLoggerOk; on the nop ones Debug..Error and Check+Write return, and
// Fatal exits with status 1 (Spec/go_uber_org/zap/Logger__Fatal.lean), checked in a child.
func TestConstructorsOk(t *testing.T) {
	childMain()
	prod, err := zap.NewProduction()
	if err != nil {
		t.Fatal(err)
	}
	dev, err := zap.NewDevelopment()
	if err != nil {
		t.Fatal(err)
	}
	nop := zap.NewNop()
	nopCases := map[string]*zap.Logger{
		"zap.NewNop()":                               nop,
		"zap.NewNop().Named(raft)":                   nop.Named("raft"),
		"zap.NewNop().With(field)":                   nop.With(zap.String("k", "v")),
		"zap.NewNop().WithOptions(AddCallerSkip(1))": nop.WithOptions(zap.AddCallerSkip(1)),
	}
	for name, l := range map[string]*zap.Logger{
		"zap.NewExample()":     zap.NewExample(),
		"zap.NewProduction()":  prod,
		"zap.NewDevelopment()": dev,
	} {
		mustHold(t, "zapLoggerOk("+name+")", ZapLoggerOk(l))
	}
	for name, l := range nopCases {
		mustHold(t, "zapLoggerOk("+name+")", ZapLoggerOk(l))
		mustReturn(t, name+": Debug, Info, Warn, Error, Check+Write", func() {
			l.Debug("x")
			l.Info("x")
			l.Warn("x")
			l.Error("x")
			if ce := l.Check(zapcore.WarnLevel, "x"); ce != nil {
				ce.Write()
			}
		})
	}
	code, out := runChild(t, "TestConstructorsOk", "fatal-nop")
	if code != 1 || strings.Contains(out, childReturned) {
		t.Fatalf("zap.NewNop().Fatal: child exit %d, expected 1; output:\n%s", code, out)
	}
	t.Logf("zap.NewNop().Fatal: child exited with status 1")
}

// ---- 3. the logger family ----

type str string

func (s str) String() string { return string(s) }

func freePorts(t *testing.T, n int) []string {
	t.Helper()
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

// srvCfg: a ServerConfig whose data directory is dir, logging to lg.
func srvCfg(lg *zap.Logger, dir string) config.ServerConfig {
	cfg := config.ServerConfig{Logger: lg, DataDir: dir}
	if err := os.MkdirAll(filepath.Dir(cfg.BackendPath()), 0o700); err != nil {
		panic(err)
	}
	return cfg
}

// rangeNoWait sends a Range through cli's RetryKVClient (the repeatable policy), so through its
// retrying interceptor, with WaitForReady(false): against an unreachable endpoint the attempts fail
// Unavailable at once, and the interceptor retries them, calling the round-robin backoff (roundRobinQuorumBackoff) from the
// second attempt on, until the timeout.
func rangeNoWait(cli *clientv3.Client, d time.Duration) error {
	ctx, cancel := context.WithTimeout(context.Background(), d)
	defer cancel()
	_, err := clientv3.RetryKVClient(cli).Range(ctx, &pb.RangeRequest{Key: []byte("k")},
		grpc.WaitForReady(false))
	return err
}

// syncBuf: a write syncer over a buffer, safe for concurrent use.
type syncBuf struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (s *syncBuf) Write(p []byte) (int, error) { s.mu.Lock(); defer s.mu.Unlock(); return s.b.Write(p) }
func (s *syncBuf) Sync() error                 { return nil }
func (s *syncBuf) String() string              { s.mu.Lock(); defer s.mu.Unlock(); return s.b.String() }

// TestFamilyZero: the logger family, one subtest per function reachable from an exported entry
// point. Each panics with the zero logger zl := &zap.Logger{} (zapLoggerOk excluded) and returns with
// zap.NewNop(); the rows whose premise is zapLoggerOrNil also return with nil. On the other rows the
// nil outcome is logged, and where nil panics that is asserted too (the premise is zapLoggerOk, not
// zapLoggerOrNil, there). The Lean statement each backs is named in its comment.
func TestFamilyZero(t *testing.T) {
	childMain()
	zl := &zap.Logger{}
	mustFail(t, "zapLoggerOk(&zap.Logger{})", ZapLoggerOk(zl))
	nop := zap.NewNop()

	// Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/WarnOfFailedRequest.lean: zapLoggerOk lg
	// (an unconditional lg.Warn).
	t.Run("txn.WarnOfFailedRequest", func(t *testing.T) {
		call := func(lg *zap.Logger) func() {
			return func() {
				txn.WarnOfFailedRequest(lg, time.Now(), str("req"), &pb.RangeResponse{}, errors.New("e"))
			}
		}
		mustPanic(t, "WarnOfFailedRequest(zl)", call(zl))
		mustReturn(t, "WarnOfFailedRequest(NewNop())", call(nop))
		mustPanic(t, "WarnOfFailedRequest(nil) [premise zapLoggerOk, not or-nil]", call(nil))
	})

	// Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/WarnOfExpensiveRequest.lean: zapLoggerOk lg
	// (with warningApplyDuration 0 and now a second ago, warnOfExpensiveGenericRequest's lg.Warn).
	t.Run("txn.WarnOfExpensiveRequest", func(t *testing.T) {
		call := func(lg *zap.Logger) func() {
			return func() {
				txn.WarnOfExpensiveRequest(lg, 0, time.Now().Add(-time.Second), str("req"),
					&pb.RangeResponse{}, nil)
			}
		}
		mustPanic(t, "WarnOfExpensiveRequest(zl, 0)", call(zl))
		mustReturn(t, "WarnOfExpensiveRequest(NewNop(), 0)", call(nop))
		mustPanic(t, "WarnOfExpensiveRequest(nil, 0) [premise zapLoggerOk, not or-nil]", call(nil))
	})

	// Spec/go_etcd_io/etcd/server/v3/storage/mvcc/hashStorage__Store.lean, through
	// Proof/go_etcd_io/etcd/server/v3/storage/mvcc/HashDefs.lean's zapLoggerOk of the hash
	// storage's logger (Store's unconditional s.lg.Info; the store is not touched before it).
	t.Run("mvcc.hashStorage.Store", func(t *testing.T) {
		call := func(lg *zap.Logger) func() {
			return func() { mvcc.NewHashStorage(lg, nil).Store(mvcc.KeyValueHash{Revision: 1}) }
		}
		mustPanic(t, "NewHashStorage(zl, nil).Store", call(zl))
		mustReturn(t, "NewHashStorage(NewNop(), nil).Store", call(nop))
		mustPanic(t, "NewHashStorage(nil, nil).Store [premise zapLoggerOk, not or-nil]", call(nil))
	})

	// Proof/go_etcd_io/etcd/pkg/v3/traceutil/Defs.lean: ownTrace's zapLoggerOrNil v.lg'
	// (Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__LogWithStepThreshold.lean logs through it when
	// non-nil).
	t.Run("traceutil.LogWithStepThreshold", func(t *testing.T) {
		call := func(lg *zap.Logger) func() {
			return func() {
				_, tr := traceutil.EnsureTrace(context.Background(), lg, "op")
				tr.Step("step")
				tr.LogWithStepThreshold(0)
			}
		}
		mustPanic(t, "EnsureTrace(zl).LogWithStepThreshold(0)", call(zl))
		mustReturn(t, "EnsureTrace(NewNop()).LogWithStepThreshold(0)", call(nop))
		mustReturn(t, "EnsureTrace(nil).LogWithStepThreshold(0) [or-nil]", call(nil))
	})

	// Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean: zapLoggerOrNil lg (nil becomes
	// zap.NewNop(); an out-of-range bcrypt cost, 0 here, logs lg.Warn first).
	t.Run("auth.NewAuthStore", func(t *testing.T) {
		be := backend.NewDefaultBackend(nop, filepath.Join(t.TempDir(), "db"))
		defer be.Close()
		tp, err := auth.NewTokenProvider(nil, "", nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		call := func(lg *zap.Logger) func() {
			return func() { auth.NewAuthStore(lg, schema.NewAuthBackend(nop, be), tp, 0) }
		}
		mustPanic(t, "NewAuthStore(zl, ..., bcryptCost 0)", call(zl))
		mustReturn(t, "NewAuthStore(NewNop(), ..., bcryptCost 0)", call(nop))
		mustReturn(t, "NewAuthStore(nil, ..., bcryptCost 0) [or-nil]", call(nil))
	})

	// Spec/go_etcd_io/etcd/server/v3/auth/newTokenProviderJWT.lean: zapLoggerOrNil lg (nil becomes
	// zap.NewNop()). "jwt,bogus=1": no sign-method, so ParseWithDefaults fails and
	// newTokenProviderJWT logs lg.Error("problem loading JWT options"); NewTokenProvider returns
	// ErrInvalidAuthOpts.
	t.Run("auth.NewTokenProvider(jwt)", func(t *testing.T) {
		call := func(lg *zap.Logger) func() {
			return func() {
				if _, err := auth.NewTokenProvider(lg, "jwt,bogus=1", nil, time.Second); err == nil {
					panic("NewTokenProvider(jwt,bogus=1) succeeded")
				}
			}
		}
		mustPanic(t, "NewTokenProvider(zl, jwt,bogus=1)", call(zl))
		mustReturn(t, "NewTokenProvider(NewNop(), jwt,bogus=1)", call(nop))
		mustReturn(t, "NewTokenProvider(nil, jwt,bogus=1) [or-nil]", call(nil))
	})

	// Spec/go_etcd_io/etcd/server/v3/storage/backend/newBoltLoggerZap.lean: zapLoggerOk
	// cfg.Logger' (backend.New makes a nil logger zap.NewNop() first, so New's own premise is
	// or-nil); bbolt's Open logs Infof through the zap bolt logger before opening the file.
	t.Run("backend.New", func(t *testing.T) {
		dir := t.TempDir()
		mk := func(lg *zap.Logger, name string) backend.BackendConfig {
			c := backend.DefaultBackendConfig(lg)
			c.Path = filepath.Join(dir, name)
			return c
		}
		mustPanic(t, "backend.New(Logger: zl)", func() { backend.New(mk(zl, "zl")) })
		mustReturn(t, "backend.New(Logger: NewNop())", func() { backend.New(mk(nop, "nop")).Close() })
		mustReturn(t, "backend.New(Logger: nil) [or-nil]", func() { backend.New(mk(nil, "nil")).Close() })
	})

	// Proof/go_etcd_io/etcd/server/v3/storage/InvOpen.lean: openPre's zapLoggerOk cfg.Logger'
	// (Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean). OpenBackend opens the backend in
	// a goroutine of its own: with zl, bbolt's Infof panics there, which crashes the process (no
	// recover can catch it), so that run is a child. With nil, the backend opens (backend.New makes
	// nil zap.NewNop()), then OpenBackend's deferred cfg.Logger.Info panics in the caller.
	t.Run("storage.OpenBackend", func(t *testing.T) {
		childPanics(t, "TestFamilyZero", "openbackend-zero", []string{"nil pointer", "bbolt"},
			"ZAPLOGGER_DIR="+t.TempDir())
		mustReturn(t, "OpenBackend(Logger: NewNop())", func() {
			storage.OpenBackend(srvCfg(nop, t.TempDir()), nil).Close()
		})
		cfg := srvCfg(nil, t.TempDir())
		mustPanic(t, "OpenBackend(Logger: nil) [premise zapLoggerOk, not or-nil]",
			func() { storage.OpenBackend(cfg, nil) })
	})

	// Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean: the snapshotter's zapLoggerOk
	// lg (Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean; its
	// final s.lg.Info). snap.New makes a nil logger zap.NewNop().
	t.Run("snap.SaveDBFrom", func(t *testing.T) {
		call := func(lg *zap.Logger, id uint64) func() {
			return func() {
				dir := t.TempDir()
				if _, err := snap.New(lg, dir).SaveDBFrom(strings.NewReader("db"), id); err != nil {
					panic(err)
				}
			}
		}
		mustPanic(t, "snap.New(zl, dir).SaveDBFrom", call(zl, 1))
		mustReturn(t, "snap.New(NewNop(), dir).SaveDBFrom", call(nop, 2))
		mustReturn(t, "snap.New(nil, dir).SaveDBFrom [nil becomes NewNop()]", call(nil, 3))
	})

	// Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Recover.lean:
	// zapLoggerOk of the cluster's logger (Recover's c.lg.Info per member recovered from the
	// backend; one member saved there first). NewCluster makes a nil logger zap.NewNop().
	t.Run("membership.RaftCluster.Recover", func(t *testing.T) {
		be := backend.NewDefaultBackend(nop, filepath.Join(t.TempDir(), "db"))
		defer be.Close()
		mb := schema.NewMembershipBackend(nop, be)
		c0 := membership.NewCluster(nop)
		c0.SetBackend(mb)
		u, _ := url.Parse("http://127.0.0.1:2380")
		c0.AddMember(membership.NewMember("m1", types.URLs{*u}, "tok", nil), membership.ApplyBoth)
		call := func(lg *zap.Logger) func() {
			return func() {
				c := membership.NewCluster(lg)
				c.SetBackend(mb)
				c.Recover(func(*zap.Logger, *semver.Version) {})
				if len(c.Members()) != 1 {
					panic("Recover did not recover the member")
				}
			}
		}
		mustPanic(t, "NewCluster(zl).Recover", call(zl))
		mustReturn(t, "NewCluster(NewNop()).Recover", call(nop))
		mustReturn(t, "NewCluster(nil).Recover [nil becomes NewNop()]", call(nil))
	})

	// Proof/go_etcd_io/etcd/client/v3/InvClient.lean and InvClientNew.lean: the client's logger is
	// zapLoggerOk (Spec/go_etcd_io/etcd/client/v3/Client__roundRobinQuorumBackoff.lean logs
	// through c.GetLogger()). With zl, clientv3.New returns, and the first Range panics at the
	// retrying interceptor's c.GetLogger().Debug("retrying of unary invoker") of attempt 0, before
	// the backoff (called from attempt 1) can be reached: the same logger, the same premise. Run in a
	// child, as the client's goroutines hold zl. With a zap logger over a buffer (an ioCore,
	// zapLoggerOk) at Debug level, the backoff's Debug("backoff") is reached and returns.
	// (Config.Logger nil makes clientv3 build its own default logger: no nil case.)
	t.Run("clientv3.roundRobinQuorumBackoff", func(t *testing.T) {
		ep := freePorts(t, 1)[0]
		childPanics(t, "TestFamilyZero", "clientv3-zero",
			[]string{"ZAPLOGGER-CLIENT-NEW-RETURNED", "unaryClientInterceptor"}, "ZAPLOGGER_ENDPOINT="+ep)
		buf := &syncBuf{}
		lg := zap.New(zapcore.NewCore(zapcore.NewJSONEncoder(zap.NewProductionEncoderConfig()), buf,
			zapcore.DebugLevel))
		mustHold(t, "zapLoggerOk(zap.New(ioCore over a buffer))", ZapLoggerOk(lg))
		for name, l := range map[string]*zap.Logger{"NewNop()": nop, "buffer logger": lg} {
			mustReturn(t, "clientv3.New(Logger: "+name+"); Range", func() {
				cli, err := clientv3.New(clientv3.Config{Logger: l, Endpoints: []string{ep}})
				if err != nil {
					panic(err)
				}
				defer cli.Close()
				if err := rangeNoWait(cli, time.Second); err == nil {
					panic("Range against an unreachable endpoint succeeded")
				}
			})
		}
		if !strings.Contains(buf.String(), `"msg":"backoff"`) {
			t.Fatalf("the backoff's Debug was not reached; log:\n%s", buf.String())
		}
		t.Logf("roundRobinQuorumBackoff's Debug(\"backoff\") reached with a zapLoggerOk logger")
	})

	// Spec/go_etcd_io/etcd/server/v3/storage/NewBackendQuota.lean: zapLoggerOk lg. Its logs are
	// under quotaLogOnce (once per process), so each run is a child. Quota < 0 logs lg.Info and > 0
	// lg.Info, both without a nil check: nil panics too (only quota 0's log is nil-guarded).
	t.Run("storage.NewBackendQuota", func(t *testing.T) {
		for _, m := range []string{"quota-zero-neg", "quota-zero-pos", "quota-nil-neg", "quota-nil-pos"} {
			childPanics(t, "TestFamilyZero", m, []string{"nil pointer"})
		}
		for _, m := range []string{"quota-nop-neg", "quota-nop-pos"} {
			childReturns(t, "TestFamilyZero", m)
		}
	})
}

// ---- the zero server ----

// TestZeroServer backs srvLoggerOk s (Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean;
// required by the server's unexported logger-family methods, e.g.
// Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__purgeFile.lean): &etcdserver.EtcdServer{}
// fails it, and its Logger() (the first line of adjustTicks and purgeFile) panics (nil lgMu).
func TestZeroServer(t *testing.T) {
	s := &etcdserver.EtcdServer{}
	mustFail(t, "srvLoggerOk(&EtcdServer{})", SrvLoggerOk(s))
	mustPanic(t, "(&EtcdServer{}).Logger()", func() { s.Logger() })
}

// ---- 4. the examples' loggers ----

// checkAll walks root's loggers and checks zapLoggerOk of every one found.
func checkAll(t *testing.T, name string, root any) int {
	t.Helper()
	fs := Loggers(root)
	seen := map[*zap.Logger]bool{}
	for _, f := range fs {
		if err := ZapLoggerOk(f.L); err != nil {
			t.Errorf("%s: %s: %v", name, f.Path, err)
			continue
		}
		seen[f.L] = true
		t.Logf("  %s: at %s", name, f.Path)
	}
	t.Logf("%s: %d *zap.Logger references reachable (%d distinct), every one zapLoggerOk",
		name, len(fs), len(seen))
	return len(fs)
}

// peerLoggers: the loggers of s's transport's peers (each *rafthttp.peer's lg), read under the
// transport's mu while the server runs (Transport.Stop drops the peers).
func peerLoggers(s *etcdserver.EtcdServer) []*zap.Logger {
	nc := field(field(reflect.ValueOf(s).Elem(), "r"), "raftNodeConfig")
	tr := field(nc, "transport").Elem().Elem() // rafthttp.Transporter -> *Transport -> Transport
	mu := (*sync.RWMutex)(unsafe.Pointer(field(tr, "mu").UnsafeAddr()))
	mu.RLock()
	defer mu.RUnlock()
	var out []*zap.Logger
	it := field(tr, "peers").MapRange()
	for it.Next() {
		p := it.Value().Elem().Elem() // Peer -> *peer -> peer
		out = append(out, field(p, "lg").Interface().(*zap.Logger))
	}
	return out
}

// TestExamplesLoggers backs the zapLoggerOk premises the examples' proofs discharge
// (Spec/github_com/mit_pdos/etcd_grove/examples/lib/cluster3/StartCluster.lean and NewClient.lean,
// over Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean's zapLoggerOk cfg.Logger'): a
// three-member cluster over cluster3.StartCluster(cfg, zap.NewNop()) and a client run a Put and a
// Get; each server passes SrvLoggerOk and its transport peers' loggers ZapLoggerOk (read while it
// runs: Stop drops the peers); after Stop, every *zap.Logger reachable from each server (s.lg, the
// lessor's, the auth store's, the backend's and bbolt's, the cluster's, the snapshotter's, the
// transport's, raft's, the hash storage's, ...) and from the client passes ZapLoggerOk.
func TestExamplesLoggers(t *testing.T) {
	dir := t.TempDir()
	wd, _ := os.Getwd()
	if err := os.Chdir(dir); err != nil {
		t.Fatal(err)
	}
	defer os.Chdir(wd)
	p := freePorts(t, 9)
	cfg := cluster3.Config{Token: "zaplg", Name1: "zaplg-1", Name2: "zaplg-2", Name3: "zaplg-3",
		Peer1: p[0], Peer2: p[1], Peer3: p[2], Client1: p[3], Client2: p[4], Client3: p[5],
		Bridge1: p[6], Bridge2: p[7], Bridge3: p[8], SnapCount: etcdstart.NoSnapCount,
		SnapCatchUp: etcdstart.NoSnapCatchUp}
	lg := zap.NewNop()
	mustHold(t, "zapLoggerOk(zap.NewNop()) [the examples' logger]", ZapLoggerOk(lg))
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
		if s.Logger() != lg {
			t.Fatalf("member %d: s.Logger() is not the examples' logger", i+1)
		}
		pls := peerLoggers(s)
		if len(pls) != 2 {
			t.Fatalf("member %d: %d transport peers, expected 2", i+1, len(pls))
		}
		for j, pl := range pls {
			mustHold(t, fmt.Sprintf("zapLoggerOk(member %d's transport peer %d's lg)", i+1, j), ZapLoggerOk(pl))
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
	for i, s := range srvs {
		if n := checkAll(t, fmt.Sprintf("member %d", i+1), s); n == 0 {
			t.Fatalf("member %d: no logger found", i+1)
		}
	}
	if n := checkAll(t, "client", cli); n == 0 {
		t.Fatal("client: no logger found")
	}
}

// TestRaftNodeLogger backs bootOk's `bv.lg' = cfg.Logger'`
// (Proof/go_etcd_io/etcd/server/v3/etcdserver/, NewServer's %Hraft: the raft node's logger is the
// configuration's; Go: server/etcdserver/bootstrap.go, bootstrapRaftFromCluster's and
// bootstrapRaftFromWAL's `lg: cfg.Logger`, which newRaftNode copies into raftNode.lg): a
// three-member cluster over cluster3.StartCluster(cfg, lg), with lg a logger of its own (over a
// buffer, so distinct from any other), and for each member the server's raftNode `lg` field (and
// its raftNodeConfig's) is the very *zap.Logger passed as the configuration's Logger.
func TestRaftNodeLogger(t *testing.T) {
	dir := t.TempDir()
	wd, _ := os.Getwd()
	if err := os.Chdir(dir); err != nil {
		t.Fatal(err)
	}
	defer os.Chdir(wd)
	p := freePorts(t, 9)
	cfg := cluster3.Config{Token: "rnlg", Name1: "rnlg-1", Name2: "rnlg-2", Name3: "rnlg-3",
		Peer1: p[0], Peer2: p[1], Peer3: p[2], Client1: p[3], Client2: p[4], Client3: p[5],
		Bridge1: p[6], Bridge2: p[7], Bridge3: p[8], SnapCount: etcdstart.NoSnapCount,
		SnapCatchUp: etcdstart.NoSnapCatchUp}
	lg := zap.New(zapcore.NewCore(zapcore.NewJSONEncoder(zap.NewProductionEncoderConfig()), &syncBuf{},
		zapcore.InfoLevel))
	mustHold(t, "zapLoggerOk(the passed logger)", ZapLoggerOk(lg))
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		t.Fatal("StartCluster failed")
	}
	defer func() {
		for _, s := range srvs {
			s.Stop()
		}
		for _, b := range brs {
			b.Close()
		}
	}()
	for i, s := range srvs {
		if s.Cfg.Logger != lg {
			t.Fatalf("member %d: s.Cfg.Logger is not the passed logger", i+1)
		}
		r := field(reflect.ValueOf(s).Elem(), "r")
		rlg := field(r, "lg").Interface().(*zap.Logger)
		clg := field(field(r, "raftNodeConfig"), "lg").Interface().(*zap.Logger)
		if rlg != s.Cfg.Logger {
			t.Fatalf("member %d: raftNode.lg %p is not cfg.Logger %p", i+1, rlg, s.Cfg.Logger)
		}
		if clg != s.Cfg.Logger {
			t.Fatalf("member %d: raftNodeConfig.lg %p is not cfg.Logger %p", i+1, clg, s.Cfg.Logger)
		}
		t.Logf("member %d: raftNode.lg == raftNodeConfig.lg == cfg.Logger (%p)", i+1, rlg)
	}
}
