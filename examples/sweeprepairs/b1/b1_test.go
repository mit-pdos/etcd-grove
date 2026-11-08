package b1

import (
	"context"
	"errors"
	"fmt"
	"math/rand"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/test/bufconn"
	"google.golang.org/protobuf/types/known/emptypb"
)

// envAtStart is ETCD_VERIFY's verdict before any test runs (B4: the startup premise).
var envAtStart = EnvVerifyOff()
var envRawAtStart = os.Getenv("ETCD_VERIFY")

func TestMain(m *testing.M) {
	fmt.Printf("B4 startup: ETCD_VERIFY=%q envVerifyOff=%v\n", envRawAtStart, envAtStart)
	os.Exit(m.Run())
}

func panics(f func()) (msg string, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			msg, ok = fmt.Sprint(r), true
		}
	}()
	f()
	return "", false
}

// ---------------------------------------------------------------------------------------------
// B1: errors.IsCtxErr's premise isCtxErr err.

type badUnwrap struct{}

func (badUnwrap) Error() string  { return "" }
func (badUnwrap) Unwrap() error { panic("Unwrap") }

type badIs struct{}

func (badIs) Error() string        { return "" }
func (badIs) Is(target error) bool { panic("Is") }

func TestB1Counterexample(t *testing.T) {
	for _, c := range []struct {
		name string
		err  error
		tgt  error
	}{{"badUnwrap/Canceled", badUnwrap{}, context.Canceled}, {"badIs/DeadlineExceeded", badIs{}, context.DeadlineExceeded}} {
		if IsCtxErr(c.err) {
			t.Fatalf("%s: isCtxErr holds of the counterexample", c.name)
		}
		msg, p := panics(func() { _ = errors.Is(c.err, c.tgt) })
		if !p {
			t.Fatalf("%s: errors.Is did not panic", c.name)
		}
		t.Logf("%s: isCtxErr=false (premise violated); errors.Is panics: %s", c.name, msg)
	}
}

func TestB1StdContexts(t *testing.T) {
	n := 0
	check := func(what string, err error) {
		n++
		if !IsCtxErr(err) {
			t.Fatalf("%s: Err() = %v is not a context error", what, err)
		}
		_ = errors.Is(err, context.Canceled)
		_ = errors.Is(err, context.DeadlineExceeded)
	}
	for i := 0; i < 200; i++ {
		ctx, cancel := context.WithCancel(context.Background())
		cancel()
		check("WithCancel", ctx.Err())
		tctx, tcancel := context.WithTimeout(context.Background(), time.Microsecond)
		<-tctx.Done()
		check("WithTimeout expired", tctx.Err())
		tcancel()
		p, pc := context.WithCancel(context.Background())
		c, cc := context.WithTimeout(p, time.Hour)
		pc()
		<-c.Done()
		check("WithTimeout of a canceled parent", c.Err())
		cc()
		cz, czc := context.WithCancelCause(context.Background())
		czc(errors.New("cause"))
		check("WithCancelCause", cz.Err())
		dz, dzc := context.WithDeadlineCause(context.Background(), time.Now(), errors.New("cause"))
		<-dz.Done()
		check("WithDeadlineCause", dz.Err())
		dzc()
		v := context.WithValue(p, auth.AuthenticateParamIndex{}, uint64(1))
		vc, vcc := context.WithTimeout(v, time.Hour)
		<-vc.Done()
		check("WithTimeout of WithValue of a canceled parent", vc.Err())
		vcc()
	}
	t.Logf("B1 standard contexts: %d Err() values, all isCtxErr", n)
}

// The gRPC side: a server registered by hand (one unary method, one bidirectional stream) over
// bufconn, as etcd's handlers see their contexts.

type rec struct {
	kind string
	ok   bool
	val  string
}

type server struct {
	out chan rec
}

type svc interface{}

var desc = grpc.ServiceDesc{
	ServiceName: "b1.T",
	HandlerType: (*svc)(nil),
	Methods: []grpc.MethodDesc{{MethodName: "U", Handler: func(srv any, ctx context.Context, dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
		in := new(emptypb.Empty)
		if err := dec(in); err != nil {
			return nil, err
		}
		return srv.(*server).unary(ctx)
	}}},
	Streams: []grpc.StreamDesc{{StreamName: "S", ServerStreams: true, ClientStreams: true,
		Handler: func(srv any, st grpc.ServerStream) error { return srv.(*server).stream(st) }}},
}

// unary: what EtcdServer.Put/Txn/LeaseRenew/processInternalRaftRequestOnce do with the handler's
// context: the start time stored with WithValue (B2), WithRoot's two values (B2), and
// `cctx, cancel := context.WithTimeout(ctx, reqTimeout)` whose `Err()` goes to `errors.Is` (B1).
func (s *server) unary(ctx context.Context) (*emptypb.Empty, error) {
	s.out <- rec{"B2 grpc handler ctx", StartTimeOk(ctx), fmt.Sprint(ctx.Value(traceutil.StartTimeKey{}))}
	put := context.WithValue(ctx, traceutil.StartTimeKey{}, time.Now())
	s.out <- rec{"B2 Put/Txn ctx (WithValue StartTimeKey time.Now())", StartTimeOk(put), ""}
	root := context.WithValue(context.WithValue(ctx, auth.AuthenticateParamIndex{}, uint64(7)),
		auth.AuthenticateParamSimpleTokenPrefix{}, "tok")
	s.out <- rec{"B2 WithRoot-shaped ctx over the handler ctx", StartTimeOk(root), ""}
	cctx, cancel := context.WithTimeout(ctx, time.Duration(rand.Intn(3000))*time.Microsecond)
	defer cancel()
	<-cctx.Done()
	err := cctx.Err()
	_ = errors.Is(err, context.DeadlineExceeded)
	_ = errors.Is(err, context.Canceled)
	s.out <- rec{"B1 cctx.Err() under the handler ctx", IsCtxErr(err), fmt.Sprint(err)}
	return &emptypb.Empty{}, nil
}

// stream: v3rpc.watchServer.Watch's select: the receive loop's error (errc) or the stream
// context's Err().
func (s *server) stream(st grpc.ServerStream) error {
	s.out <- rec{"B2 grpc stream ctx", StartTimeOk(st.Context()), ""}
	errc := make(chan error, 1)
	go func() {
		for {
			m := new(emptypb.Empty)
			if err := st.RecvMsg(m); err != nil {
				errc <- err
				return
			}
		}
	}()
	select {
	case err := <-errc:
		_ = errors.Is(err, context.Canceled)
		s.out <- rec{"B1 Watch errc (recvLoop's error)", IsCtxErr(err), fmt.Sprint(err)}
	case <-st.Context().Done():
		err := st.Context().Err()
		_ = errors.Is(err, context.Canceled)
		s.out <- rec{"B1 Watch stream.Context().Err()", IsCtxErr(err), fmt.Sprint(err)}
		rerr := <-errc
		_ = errors.Is(rerr, context.Canceled)
		s.out <- rec{"B1 Watch errc (recvLoop's error)", IsCtxErr(rerr), fmt.Sprint(rerr)}
	}
	return nil
}

func TestB1B2Grpc(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	srv := &server{out: make(chan rec, 1<<16)}
	gs := grpc.NewServer()
	gs.RegisterService(&desc, srv)
	go gs.Serve(lis)
	defer gs.Stop()
	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	const N = 150
	var wg sync.WaitGroup
	for i := 0; i < N; i++ {
		wg.Add(2)
		go func(i int) { // unary: client deadline, client cancel, or none
			defer wg.Done()
			ctx, cancel := context.WithTimeout(context.Background(), time.Duration(rand.Intn(3000))*time.Microsecond)
			if i%3 == 1 {
				go func() { time.Sleep(time.Duration(rand.Intn(2000)) * time.Microsecond); cancel() }()
			}
			if i%3 == 2 {
				cancel()
				ctx, cancel = context.WithCancel(context.Background())
			}
			defer cancel()
			_ = conn.Invoke(ctx, "/b1.T/U", &emptypb.Empty{}, new(emptypb.Empty))
		}(i)
		go func(i int) { // stream: the client sends a few messages, then cancels
			defer wg.Done()
			ctx, cancel := context.WithCancel(context.Background())
			cs, err := conn.NewStream(ctx, &desc.Streams[0], "/b1.T/S")
			if err != nil {
				cancel()
				return
			}
			for j := 0; j < i%4; j++ {
				_ = cs.SendMsg(&emptypb.Empty{})
			}
			time.Sleep(time.Duration(rand.Intn(1000)) * time.Microsecond)
			cancel()
		}(i)
	}
	wg.Wait()
	time.Sleep(200 * time.Millisecond)
	gs.Stop()
	close(srv.out)
	type cnt struct{ ok, bad int; ex string }
	counts := map[string]*cnt{}
	for r := range srv.out {
		c := counts[r.kind]
		if c == nil {
			c = &cnt{}
			counts[r.kind] = c
		}
		if r.ok {
			c.ok++
		} else {
			c.bad++
			c.ex = r.val
		}
	}
	for k, c := range counts {
		t.Logf("%-55s holds %4d, fails %4d %s", k, c.ok, c.bad, c.ex)
	}
	for k, c := range counts {
		if k == "B1 Watch errc (recvLoop's error)" {
			if c.ok != 0 {
				t.Errorf("%s: expected the gRPC stream error never to be a context error", k)
			}
			continue
		}
		if c.bad != 0 {
			t.Errorf("%s: premise fails %d times", k, c.bad)
		}
	}
}

// ---------------------------------------------------------------------------------------------
// B2: context.ValueStartTime's premise startTimeOk ctx.

type panicValueCtx struct{ context.Context }

func (panicValueCtx) Value(any) any { panic("Value") }

func TestB2Counterexample(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	c := context.WithValue(ctx, traceutil.StartTimeKey{}, 42)
	if StartTimeOk(c) {
		t.Fatal("startTimeOk holds of WithValue(StartTimeKey{}, 42)")
	}
	_, isInt := c.Value(traceutil.StartTimeKey{}).(int)
	t.Logf("WithValue(ctx, StartTimeKey{}, 42): startTimeOk=false (premise violated); Value is an int: %v", isInt)
	p := panicValueCtx{ctx}
	if StartTimeOk(p) {
		t.Fatal("startTimeOk holds of a context whose Value panics")
	}
	t.Logf("a user Context embedding a cancelCtx, Value panicking: startTimeOk=false (why `returns some value` alone is not true of every isContext)")
}

func TestB2StdContexts(t *testing.T) {
	sctx, cancel := context.WithCancel(context.Background()) // EtcdServer.s.ctx
	defer cancel()
	root := context.WithValue(context.WithValue(sctx, auth.AuthenticateParamIndex{}, uint64(3)),
		auth.AuthenticateParamSimpleTokenPrefix{}, "x") // authStore.WithRoot(s.ctx), revokeExpiredLeases
	for _, c := range []struct {
		n string
		c context.Context
	}{{"s.ctx = WithCancel(Background())", sctx}, {"WithRoot(s.ctx)", root},
		{"WithValue(StartTimeKey{}, time.Now()) over WithRoot(s.ctx)", context.WithValue(root, traceutil.StartTimeKey{}, time.Now())},
		{"Background()", context.Background()}, {"TODO()", context.TODO()}} {
		if !StartTimeOk(c.c) {
			t.Fatalf("%s: startTimeOk fails", c.n)
		}
		t.Logf("%s: startTimeOk holds", c.n)
	}
}

// ---------------------------------------------------------------------------------------------
// B3: http.Handle_ok's premises litPathPat pat and handlerRegOk h.

type nopHandler struct{}

func (nopHandler) ServeHTTP(http.ResponseWriter, *http.Request) {}

func TestB3Counterexample(t *testing.T) {
	cases := []struct {
		name string
		pats []string
		h    http.Handler
	}{{"empty pattern, nil handler", []string{""}, nil}, {"nil handler", []string{"/a"}, nil},
		{"nil HandlerFunc", []string{"/a"}, http.HandlerFunc(nil)},
		{"unparsable", []string{"b"}, nopHandler{}}, {"conflict", []string{"/{x}", "/{y}"}, nopHandler{}},
		{"escape alias", []string{"/a", "/%61"}, nopHandler{}}}
	for _, c := range cases {
		prem := HandlerRegOk(c.h)
		for _, p := range c.pats {
			prem = prem && LitPathPat(p)
		}
		if prem {
			t.Fatalf("%s: the new premises hold", c.name)
		}
		m := http.NewServeMux()
		msg, p := panics(func() {
			for _, pat := range c.pats {
				m.Handle(pat, c.h)
			}
		})
		t.Logf("%-28s premises=false; Handle panics=%v %q", c.name, p, msg)
		if !p {
			t.Errorf("%s: Handle did not panic", c.name)
		}
	}
}

func TestB3Rafthttp(t *testing.T) {
	tr := &rafthttp.Transport{Logger: zap.NewNop()}
	h := tr.Handler()
	pats := []string{rafthttp.RaftPrefix, rafthttp.RaftStreamPrefix + "/", rafthttp.RaftSnapshotPrefix, rafthttp.ProbingPrefix}
	seen := map[string]bool{}
	for _, p := range pats {
		if !LitPathPat(p) || seen[p] {
			t.Fatalf("pattern %q: litPathPat=%v, duplicate=%v", p, LitPathPat(p), seen[p])
		}
		seen[p] = true
		r := httptest.NewRequest("GET", p, nil)
		hh, got := h.(*http.ServeMux).Handler(r)
		if got != p || !HandlerRegOk(hh) {
			t.Fatalf("pattern %q: routed to %q, handler %T, handlerRegOk=%v", p, got, hh, HandlerRegOk(hh))
		}
		t.Logf("rafthttp pattern %-16q litPathPat=true, handler %T handlerRegOk=true", p, hh)
	}
}

// Distinct literal patterns never conflict: random ones registered on fresh muxes.
func TestB3RandomLiteral(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	const alpha = "ab/._-~:}+=!*$"
	muxes, regs := 0, 0
	for i := 0; i < 2000; i++ {
		m := http.NewServeMux()
		muxes++
		seen := map[string]bool{}
		for j := 0; j < 30; j++ {
			b := []byte{'/'}
			for k := rng.Intn(10); k > 0; k-- {
				b = append(b, alpha[rng.Intn(len(alpha))])
			}
			p := string(b)
			if seen[p] || !LitPathPat(p) {
				continue
			}
			seen[p] = true
			if msg, pn := panics(func() { m.Handle(p, nopHandler{}) }); pn {
				t.Fatalf("distinct literal %q panicked: %s", p, msg)
			}
			regs++
		}
	}
	t.Logf("GODEBUG=%q: %d muxes, %d registrations of distinct literal patterns, 0 panics", os.Getenv("GODEBUG"), muxes, regs)
}

func TestB3RandomLiteralMux121(t *testing.T) {
	if os.Getenv("B1_CHILD") != "" {
		t.Skip("child")
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestB3RandomLiteral$", "-test.v", "-test.count=1")
	cmd.Env = append(os.Environ(), "GODEBUG=httpmuxgo121=1", "B1_CHILD=1")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("child: %v\n%s", err, out)
	}
	t.Logf("child (old mux):\n%s", out)
}

// ---------------------------------------------------------------------------------------------
// B4: envVerifyOff.

func TestB4Startup(t *testing.T) {
	if !envAtStart {
		t.Fatalf("ETCD_VERIFY=%q at start: envVerifyOff fails", envRawAtStart)
	}
	t.Logf("ETCD_VERIFY=%q at test start: envVerifyOff holds", envRawAtStart)
}

func realBackend(t *testing.T) backend.Backend {
	be := backend.NewDefaultBackend(zap.NewNop(), filepath.Join(t.TempDir(), "db"))
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeCreateBucket(schema.Key)
	tx.UnsafePut(schema.Key, []byte("k"), []byte("v"))
	tx.Unlock()
	be.ForceCommit()
	return be
}

func TestB4Off(t *testing.T) {
	t.Setenv("ETCD_VERIFY", "")
	if !EnvVerifyOff() {
		t.Fatal("not off")
	}
	lg := zap.NewNop()
	be := realBackend(t)
	defer be.Close()
	n := 0
	for i := 0; i < 100; i++ {
		if msg, p := panics(func() {
			backend.ValidateCalledInsideApply(lg)
			backend.ValidateCalledOutSideApply(lg)
			backend.ValidateCalledInsideUnittest(lg)
			be.BatchTx().LockInsideApply()
			be.BatchTx().Unlock()
			be.BatchTx().LockOutsideApply()
			be.BatchTx().Unlock()
			backend.VerifyBackendConsistency(be, lg, true, schema.Key)
		}); p {
			t.Fatalf("panicked with ETCD_VERIFY off: %s", msg)
		}
		n++
	}
	t.Logf("ETCD_VERIFY off: %d rounds of the four functions and the real backend's locks, 0 panics", n)
}

func TestB4On(t *testing.T) {
	for _, v := range []string{"all", "lock", "ALL", "Lock"} {
		t.Setenv("ETCD_VERIFY", v)
		if EnvVerifyOff() {
			t.Fatalf("ETCD_VERIFY=%s: envVerifyOff holds", v)
		}
		msg, p := panics(func() { backend.ValidateCalledInsideApply(zap.NewNop()) })
		t.Logf("ETCD_VERIFY=%-5s envVerifyOff=false (premise violated); ValidateCalledInsideApply(Nop) outside apply panics=%v %q", v, p, msg)
		if !p {
			t.Errorf("ETCD_VERIFY=%s: no panic", v)
		}
		be := realBackend(t)
		be.SetTxPostLockInsideApplyHook(func() {}) // as the server sets it (NewServer)
		tx := be.BatchTx()
		msg, p = panics(func() { defer tx.Unlock(); tx.LockInsideApply() })
		t.Logf("ETCD_VERIFY=%-5s the real backend's LockInsideApply (hook set) outside apply panics=%v %q", v, p, msg)
		be.Close()
	}
	t.Setenv("ETCD_VERIFY", "assert")
	msg, p := panics(func() { backend.VerifyBackendConsistency(badBackend{}, nil, false) })
	t.Logf("ETCD_VERIFY=assert envVerifyOff=%v; VerifyBackendConsistency(badBackend{}) panics=%v %q", EnvVerifyOff(), p, msg)
}

type badBackend struct{ backend.Backend }
