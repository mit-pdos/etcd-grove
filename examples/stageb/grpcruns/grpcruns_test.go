// Package grpcruns checks, in Go, the claims of stage B's Scope (grpc's handler runs on real
// forks; /shared/tmp/stageB/scope-r5.md, §7 "Go test plan", and §2.2 "The trusted Serve model and
// its leaves") about grpc-go v1.84.0 and etcd's v3rpc server (the fork upamanyus/etcd at the
// examples' pin, a4d2bb1720b9). Each TestT<n> supports the claim of the Scope's row T<n>; its
// comment says which part of the trusted Serve model (Serve's loop, acceptRun, acceptRunConns,
// respond, finishStream, the pair) it backs, and cites grpc's source
// (/root/go/pkg/mod/google.golang.org/grpc@v1.84.0/) by file:line.
//
// The plain-grpc tests serve a small hand-written service (grpc.ServiceDesc over protobuf's
// wrapperspb.BytesValue) on loopback TCP; T3, T4 and T9 start a real one-member etcd as the
// examples do (examples/lib/etcdstart: StartServer, then v3rpc.Server served by gs.Serve(l)),
// with an extra innermost stream interceptor where a test needs to observe the handler. T6, T7
// and part of T9 inspect sources (the examples', and the pinned etcd and grpc modules' from the
// module cache, located with `go list -m`).
//
// A claim found false would be marked "SCOPE CLAIM FALSE" at its test, which then asserts what Go
// really does. Side findings that are not Scope claims are marked "NOTE".
package grpcruns

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"io/fs"
	"math"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"runtime"
	"runtime/pprof"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"
	"google.golang.org/grpc/keepalive"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/wrapperspb"
)

// ---------------------------------------------------------------------------------------------
// Helpers: a hand-written service, a server on loopback, a client, goroutine identities.

type msg = wrapperspb.BytesValue

type unaryFn func(ctx context.Context, req *msg) (*msg, error)

// unary is the MethodDesc of method name of service svc, whose handler is f, called through the
// server's unary interceptor as protoc-gen-go-grpc's generated handlers do.
func unary(svc, name string, f unaryFn) grpc.MethodDesc {
	full := "/" + svc + "/" + name
	return grpc.MethodDesc{MethodName: name, Handler: func(srv any, ctx context.Context,
		dec func(any) error, ic grpc.UnaryServerInterceptor) (any, error) {
		in := new(msg)
		if err := dec(in); err != nil {
			return nil, err
		}
		if ic == nil {
			return f(ctx, in)
		}
		info := &grpc.UnaryServerInfo{Server: srv, FullMethod: full}
		return ic(ctx, in, info, func(ctx context.Context, req any) (any, error) {
			return f(ctx, req.(*msg))
		})
	}}
}

// stream is the bidirectional StreamDesc of stream name, whose handler is f.
func stream(name string, f grpc.StreamHandler) grpc.StreamDesc {
	return grpc.StreamDesc{StreamName: name, Handler: f, ServerStreams: true, ClientStreams: true}
}

func service(name string, ms []grpc.MethodDesc, ss []grpc.StreamDesc) *grpc.ServiceDesc {
	return &grpc.ServiceDesc{ServiceName: name, HandlerType: (*any)(nil), Methods: ms, Streams: ss}
}

// server is a grpc.Server serving on a loopback listener, Serve's result on served.
type server struct {
	gs     *grpc.Server
	lis    net.Listener
	addr   string
	served chan error
}

// serve builds a grpc.Server with opts and the services sds, and runs gs.Serve(l) on a goroutine
// (l a loopback listener, wrapped by wrap if not nil), as the examples do.
func serve(t *testing.T, wrap func(net.Listener) net.Listener, opts []grpc.ServerOption,
	sds ...*grpc.ServiceDesc) *server {
	t.Helper()
	gs := grpc.NewServer(opts...)
	for _, sd := range sds {
		gs.RegisterService(sd, struct{}{})
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := l.Addr().String()
	var sl net.Listener = l
	if wrap != nil {
		sl = wrap(l)
	}
	s := &server{gs: gs, lis: sl, addr: addr, served: make(chan error, 1)}
	go func() { s.served <- gs.Serve(sl) }()
	t.Cleanup(gs.Stop)
	return s
}

func dial(t *testing.T, addr string, opts ...grpc.DialOption) *grpc.ClientConn {
	t.Helper()
	opts = append([]grpc.DialOption{grpc.WithTransportCredentials(insecure.NewCredentials())},
		opts...)
	cc, err := grpc.NewClient(addr, opts...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cc.Close() })
	return cc
}

func invoke(cc *grpc.ClientConn, ctx context.Context, method string, in []byte) (*msg, error) {
	out := new(msg)
	err := cc.Invoke(ctx, method, &msg{Value: in}, out)
	return out, err
}

func ctxT(t *testing.T, d time.Duration) context.Context {
	ctx, cancel := context.WithTimeout(context.Background(), d)
	t.Cleanup(cancel)
	return ctx
}

func wantCode(t *testing.T, what string, err error, c codes.Code) {
	t.Helper()
	if status.Code(err) != c {
		t.Fatalf("%s: got %v (code %v), want code %v", what, err, status.Code(err), c)
	}
}

// goid is the current goroutine's id (runtime.Stack's first line, "goroutine N [running]:").
func goid() uint64 {
	var b [64]byte
	n := runtime.Stack(b[:], false)
	f := strings.Fields(string(b[:n]))
	id, err := strconv.ParseUint(f[1], 10, 64)
	if err != nil {
		panic(err)
	}
	return id
}

// myStack is the current goroutine's stack, with its "created by" line.
func myStack() string {
	b := make([]byte, 1<<16)
	return string(b[:runtime.Stack(b, false)])
}

// allStacks is every goroutine's stack (the panic format).
func allStacks() string {
	var b bytes.Buffer
	pprof.Lookup("goroutine").WriteTo(&b, 2)
	return b.String()
}

// createdByServeStreams: the goroutine was started by serveStreams' `go f()` (server.go:1107),
// not by a stream worker (server.go:705-720, NumStreamWorkers).
func createdByServeStreams(st string) bool {
	return strings.Contains(st, "created by google.golang.org/grpc.(*Server).serveStreams")
}

// barrier: each of K arrivals blocks until all K arrived (or the timeout passes).
type barrier struct {
	k    int64
	n    atomic.Int64
	all  chan struct{}
	gids sync.Map
	bad  atomic.Int64 // arrivals not created by serveStreams' go f()
}

func newBarrier(k int) *barrier { return &barrier{k: int64(k), all: make(chan struct{})} }

func (b *barrier) arrive() error {
	b.gids.Store(goid(), true)
	if !createdByServeStreams(myStack()) {
		b.bad.Add(1)
	}
	if b.n.Add(1) == b.k {
		close(b.all)
	}
	select {
	case <-b.all:
		return nil
	case <-time.After(20 * time.Second):
		return status.Error(codes.DeadlineExceeded, "barrier timeout")
	}
}

func (b *barrier) distinct() int {
	n := 0
	b.gids.Range(func(_, _ any) bool { n++; return true })
	return n
}

// ---------------------------------------------------------------------------------------------
// A real one-member etcd, served as examples/lib/etcdstart.Serve does (v3rpc.Server with the
// keepalive policy, gs.Serve(l) on a goroutine), with extra options appended (an innermost
// interceptor). etcdstart.Serve does not return the *grpc.Server, hence the copy.

func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return l.Addr().String()
}

func startEtcd(t *testing.T, name string, extra ...grpc.ServerOption) (*grpc.Server, string) {
	t.Helper()
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	caddr := freeAddr(t)
	s, err := etcdstart.StartServer(name, freeAddr(t), caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(s.Stop)
	opts := append([]grpc.ServerOption{grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
		MinTime: 5 * time.Second,
	})}, extra...)
	gs := v3rpc.Server(s, nil, nil, opts...)
	l, err := net.Listen("tcp", caddr)
	if err != nil {
		t.Fatal(err)
	}
	go gs.Serve(l)
	t.Cleanup(gs.Stop)
	select {
	case <-s.ReadyNotify():
	case <-time.After(20 * time.Second):
		t.Fatal("etcd not ready")
	}
	return gs, caddr
}

// srvOpts is the grpc.Server's (unexported) serverOptions, read by reflection.
func srvOpts(gs *grpc.Server) reflect.Value {
	return reflect.ValueOf(gs).Elem().FieldByName("opts")
}

// ---------------------------------------------------------------------------------------------
// Source helpers: a module's directory in the module cache, a parsed Go file.

func modDir(t *testing.T, mod string) string {
	t.Helper()
	out, err := exec.Command("go", "list", "-m", "-f", "{{.Dir}}", mod).Output()
	if err != nil {
		t.Fatalf("go list -m %s: %v", mod, err)
	}
	d := strings.TrimSpace(string(out))
	if d == "" {
		t.Fatalf("go list -m %s: no directory", mod)
	}
	return d
}

func parseFile(t *testing.T, path string) (*token.FileSet, *ast.File) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	return fset, f
}

func funcDecl(f *ast.File, recv, name string) *ast.FuncDecl {
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || fd.Name.Name != name {
			continue
		}
		r := ""
		if fd.Recv != nil && len(fd.Recv.List) > 0 {
			switch x := fd.Recv.List[0].Type.(type) {
			case *ast.StarExpr:
				r = x.X.(*ast.Ident).Name
			case *ast.Ident:
				r = x.Name
			}
		}
		if r == recv {
			return fd
		}
	}
	return nil
}

// selCall: n is a call x.sel(...) where x is the identifier recvName ("" for any receiver).
func selCall(n ast.Node, recvName, sel string) bool {
	c, ok := n.(*ast.CallExpr)
	if !ok {
		return false
	}
	s, ok := c.Fun.(*ast.SelectorExpr)
	if !ok || s.Sel.Name != sel {
		return false
	}
	if recvName == "" {
		return true
	}
	id, ok := s.X.(*ast.Ident)
	return ok && id.Name == recvName
}

func contains(n ast.Node, pred func(ast.Node) bool) bool {
	found := false
	ast.Inspect(n, func(m ast.Node) bool {
		if m != nil && pred(m) {
			found = true
		}
		return !found
	})
	return found
}

func countIn(n ast.Node, pred func(ast.Node) bool) int {
	k := 0
	ast.Inspect(n, func(m ast.Node) bool {
		if m != nil && pred(m) {
			k++
		}
		return true
	})
	return k
}

// =============================================================================================
// T1. Scope §7 T1 ("the bug; one fork per call"), §2.2 Serve's `go model.runCall`: K = 2048
// concurrent unary calls, and separately K concurrent streams, give K concurrent handler
// goroutines, each started by serveStreams' `go f()` (server.go:1090-1107; the stream quota is
// maxConcurrentStreams, math.MaxUint32 by default, server.go:189, and etcd sets it from
// MaxConcurrentStreams, also math.MaxUint32 by default). So grpc spawns an unbounded number of
// handler goroutines: the count of running handlers is not bounded by anything in grpc.
func TestT1ConcurrentHandlers(t *testing.T) {
	const K = 2048
	run := func(t *testing.T, streams bool) {
		b := newBarrier(K)
		sd := service("t1.S",
			[]grpc.MethodDesc{unary("t1.S", "U", func(ctx context.Context, in *msg) (*msg, error) {
				return in, b.arrive()
			})},
			[]grpc.StreamDesc{stream("St", func(srv any, ss grpc.ServerStream) error {
				return b.arrive()
			})})
		s := serve(t, nil, []grpc.ServerOption{grpc.MaxConcurrentStreams(math.MaxUint32)}, sd)
		cc := dial(t, s.addr)
		ctx := ctxT(t, 30*time.Second)
		var wg sync.WaitGroup
		errs := make(chan error, K)
		for i := 0; i < K; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				if !streams {
					_, err := invoke(cc, ctx, "/t1.S/U", []byte("x"))
					if err != nil {
						errs <- err
					}
					return
				}
				cs, err := cc.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true},
					"/t1.S/St")
				if err != nil {
					errs <- err
					return
				}
				cs.CloseSend()
				if err := cs.RecvMsg(new(msg)); err != io.EOF {
					errs <- fmt.Errorf("RecvMsg: %v", err)
				}
			}()
		}
		wg.Wait()
		close(errs)
		for err := range errs {
			t.Fatalf("call failed: %v", err)
		}
		if got := b.n.Load(); got != K {
			t.Fatalf("handlers run: %d, want %d", got, K)
		}
		if d := b.distinct(); d != K {
			t.Fatalf("distinct handler goroutines while all %d were blocked: %d", K, d)
		}
		if bad := b.bad.Load(); bad != 0 {
			t.Fatalf("%d handlers not on a goroutine created by serveStreams' go f()", bad)
		}
	}
	t.Run("unary", func(t *testing.T) { run(t, false) })
	t.Run("streams", func(t *testing.T) { run(t, true) })
}

// =============================================================================================
// T2. Scope §7 T2 ("asynchronous Invoke"; §2.2 "The pair": an Invoke that returns an error early
// leaves its deposit with the run): a unary handler finishes, with an observable side effect,
// after its client's Invoke returned DeadlineExceeded. grpc does not wait for, nor stop, the
// handler when the client gives up: the handler's context is cancelled, nothing more.
func TestT2HandlerOutlivesDeadline(t *testing.T) {
	var started, finished atomic.Bool
	ctxDone := make(chan bool, 1)
	sd := service("t2.S", []grpc.MethodDesc{unary("t2.S", "U",
		func(ctx context.Context, in *msg) (*msg, error) {
			started.Store(true)
			time.Sleep(500 * time.Millisecond) // ignores ctx
			ctxDone <- ctx.Err() != nil
			finished.Store(true)
			return in, nil
		})}, nil)
	s := serve(t, nil, nil, sd)
	cc := dial(t, s.addr)
	// warm up the connection, so the deadline is spent in the handler
	if err := cc.Invoke(ctxT(t, 5*time.Second), "/t2.S/none", &msg{}, new(msg)); status.Code(err) != codes.Unimplemented {
		t.Fatalf("warm-up: %v", err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()
	_, err := invoke(cc, ctx, "/t2.S/U", []byte("x"))
	wantCode(t, "Invoke", err, codes.DeadlineExceeded)
	if !started.Load() {
		t.Fatal("handler had not started when Invoke returned")
	}
	if finished.Load() {
		t.Fatal("handler had already finished when Invoke returned DeadlineExceeded")
	}
	select {
	case cancelled := <-ctxDone:
		if !cancelled {
			t.Errorf("the handler's context was not cancelled after the client's deadline")
		}
	case <-time.After(5 * time.Second):
		t.Fatal("handler never finished")
	}
	if !finished.Load() {
		t.Fatal("handler did not finish")
	}
}

// =============================================================================================
// T3. Scope §7 T3 ("the loops' own tokens"): etcd's Watch handler (v3rpc/watch.go,
// watchServer.Watch) starts sendLoop (waited for by sws.close's wg.Wait) and recvLoop (not
// waited for: watch.go's own comment says recvLoop's Recv may keep blocking after the handler's
// context is done). On a real etcd we make Watch return while recvLoop is blocked, the way etcd's
// own stream interceptor does with WithRequireLeader (interceptor.go:239-257: the stream wrapped
// in serverStreamWithCtx, whose context is cancelled on leader loss): an innermost stream
// interceptor wraps the stream with a context of its own and cancels it. When the handler has
// returned, and before grpc finishes the stream, the interceptor dumps all goroutines: recvLoop
// is still running and sendLoop is gone. So a loop of a stream handler outlives the handler's
// return (and needs its own thread token, not the run's).
type ctxStream struct {
	grpc.ServerStream
	ctx context.Context
}

func (c ctxStream) Context() context.Context { return c.ctx }

func TestT3WatchLoopOutlivesHandler(t *testing.T) {
	type report struct {
		err            error
		recvLoopAlive  bool
		sendLoopAlive  bool
		handlerReturns bool
	}
	cancelc := make(chan context.CancelFunc, 1)
	reports := make(chan report, 1)
	icpt := func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo,
		h grpc.StreamHandler) error {
		if info.FullMethod != "/etcdserverpb.Watch/Watch" {
			return h(srv, ss)
		}
		ctx, cancel := context.WithCancel(ss.Context())
		cancelc <- cancel
		err := h(srv, ctxStream{ss, ctx})
		st := allStacks()
		reports <- report{
			err:            err,
			recvLoopAlive:  strings.Contains(st, "v3rpc.(*serverWatchStream).recvLoop"),
			sendLoopAlive:  strings.Contains(st, "v3rpc.(*serverWatchStream).sendLoop"),
			handlerReturns: true,
		}
		return err
	}
	_, addr := startEtcd(t, "t3", grpc.ChainStreamInterceptor(icpt))
	cc := dial(t, addr)
	wc, err := pb.NewWatchClient(cc).Watch(ctxT(t, 20*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if err := wc.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: []byte("t3")}}}); err != nil {
		t.Fatal(err)
	}
	r, err := wc.Recv()
	if err != nil || !r.Created {
		t.Fatalf("watch create: %v %v", r, err)
	}
	// both loops are running now; the client sends nothing more, so recvLoop blocks in Recv
	cancel := <-cancelc
	cancel()
	var rep report
	select {
	case rep = <-reports:
	case <-time.After(10 * time.Second):
		t.Fatal("Watch handler did not return after its context was cancelled")
	}
	t.Logf("Watch returned %v; at its return recvLoop alive=%v, sendLoop alive=%v", rep.err,
		rep.recvLoopAlive, rep.sendLoopAlive)
	if !rep.recvLoopAlive {
		t.Fatal("recvLoop was not running when the Watch handler returned")
	}
	if rep.sendLoopAlive {
		t.Fatal("sendLoop still running when Watch returned (sws.close waits for it)")
	}
	// recvLoop ends once grpc finishes the stream (its Recv fails)
	deadline := time.Now().Add(10 * time.Second)
	for strings.Contains(allStacks(), "v3rpc.(*serverWatchStream).recvLoop") {
		if time.Now().After(deadline) {
			t.Fatal("recvLoop never ended")
		}
		time.Sleep(20 * time.Millisecond)
	}
}

// =============================================================================================
// T4. Scope §7 T4 ("the model's fork"; §2.2 Serve's `go model.runCall`): etcd's v3rpc.Server
// (v3rpc/grpc.go, Server) does not set NumStreamWorkers (server.go:635-645), so every stream is
// handled on a fresh goroutine by serveStreams' `go f()` (server.go:1099-1107; with workers,
// server.go:1099-1104 would hand f to a pooled goroutine instead). Checked twice on a real etcd
// served as the examples serve it: the server's numServerWorkers is 0 (by reflection), and N
// concurrent Watch streams run on N distinct goroutines, each created by serveStreams.
func TestT4EtcdNoStreamWorkers(t *testing.T) {
	const N = 16
	b := newBarrier(N)
	icpt := func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo,
		h grpc.StreamHandler) error {
		if info.FullMethod == "/etcdserverpb.Watch/Watch" {
			if err := b.arrive(); err != nil {
				return err
			}
		}
		return h(srv, ss)
	}
	gs, addr := startEtcd(t, "t4", grpc.ChainStreamInterceptor(icpt))
	if w := srvOpts(gs).FieldByName("numServerWorkers").Uint(); w != 0 {
		t.Fatalf("etcd's grpc server has numServerWorkers = %d", w)
	}
	cc := dial(t, addr)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	for i := 0; i < N; i++ {
		// raw streams (clientv3's Watch would multiplex watches on one stream)
		wc, err := pb.NewWatchClient(cc).Watch(ctx)
		if err != nil {
			t.Fatal(err)
		}
		if err := wc.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
			CreateRequest: &pb.WatchCreateRequest{Key: []byte("t4")}}}); err != nil {
			t.Fatal(err)
		}
	}
	select {
	case <-b.all:
	case <-time.After(20 * time.Second):
		t.Fatalf("only %d of %d Watch streams reached their handlers", b.n.Load(), N)
	}
	if d := b.distinct(); d != N {
		t.Fatalf("%d concurrent Watch streams on %d goroutines", N, d)
	}
	if bad := b.bad.Load(); bad != 0 {
		t.Fatalf("%d Watch streams not on a goroutine created by serveStreams' go f()", bad)
	}
}

// =============================================================================================
// T5. Scope §7 T5 ("Serve's returns; stopped (S-m1)"; §2.2 acceptRun's `stopped` and
// `lisFailed`): Serve returns nil after Stop and after GracefulStop (server.go:916-922: the
// deferred wait on s.done, and :971/:980), and a non-nil error when the listener is closed
// (server.go:982, Accept's error is not Temporary). After a nil return, no call starts a
// handler: calls on the connection that was open, and on a new one, fail without a handler run
// (Stop/GracefulStop removed every connection and closed every listener, server.go:1687-1711).
//
// NOTE (not tested, inherent race): a stream whose `go f()` (server.go:1107) was spawned before
// Stop closed its connection could reach its handler after Serve returned: f is counted in
// handlersWG, which Stop waits for only with WaitForHandlers (server.go:1720), not in serveWG.
// That is consistent with the model, where the fork (`go model.runCall`) happens inside Serve's
// loop, before the `stopped` return; what Go guarantees, and what this test checks, is that no
// call is accepted (delivered) after the return.
func TestT5ServeReturns(t *testing.T) {
	newSrv := func(t *testing.T) (*server, *atomic.Int64) {
		var runs atomic.Int64
		sd := service("t5.S", []grpc.MethodDesc{unary("t5.S", "U",
			func(ctx context.Context, in *msg) (*msg, error) {
				runs.Add(1)
				return in, nil
			})}, nil)
		return serve(t, nil, nil, sd), &runs
	}
	waitServe := func(t *testing.T, s *server) error {
		select {
		case err := <-s.served:
			return err
		case <-time.After(10 * time.Second):
			t.Fatal("Serve did not return")
			return nil
		}
	}
	for _, stop := range []string{"Stop", "GracefulStop"} {
		t.Run(stop, func(t *testing.T) {
			s, runs := newSrv(t)
			cc := dial(t, s.addr)
			if _, err := invoke(cc, ctxT(t, 5*time.Second), "/t5.S/U", nil); err != nil {
				t.Fatal(err)
			}
			if stop == "Stop" {
				s.gs.Stop()
			} else {
				s.gs.GracefulStop()
			}
			if err := waitServe(t, s); err != nil {
				t.Fatalf("Serve after %s returned %v, want nil", stop, err)
			}
			before := runs.Load()
			for i := 0; i < 3; i++ {
				if _, err := invoke(cc, ctxT(t, 300*time.Millisecond), "/t5.S/U", nil); err == nil {
					t.Fatal("a call on the open connection succeeded after Serve returned nil")
				}
				cc2 := dial(t, s.addr)
				if _, err := invoke(cc2, ctxT(t, 300*time.Millisecond), "/t5.S/U", nil); err == nil {
					t.Fatal("a call on a new connection succeeded after Serve returned nil")
				}
			}
			if after := runs.Load(); after != before {
				t.Fatalf("%d handler runs started after Serve returned nil", after-before)
			}
			// Serve again on a stopped server: ErrServerStopped (server.go:910-915)
			l, _ := net.Listen("tcp", "127.0.0.1:0")
			if err := s.gs.Serve(l); !errors.Is(err, grpc.ErrServerStopped) {
				t.Fatalf("Serve after %s: %v", stop, err)
			}
		})
	}
	t.Run("listener closed", func(t *testing.T) {
		s, _ := newSrv(t)
		cc := dial(t, s.addr)
		if _, err := invoke(cc, ctxT(t, 5*time.Second), "/t5.S/U", nil); err != nil {
			t.Fatal(err)
		}
		s.lis.Close()
		err := waitServe(t, s)
		if err == nil {
			t.Fatal("Serve returned nil after its listener was closed")
		}
		t.Logf("Serve after the listener's close returned %v", err)
	})
}

// =============================================================================================
// T5b. Scope §7 T5b ("acceptRunConns"; §2.2 model.serveRest): after a listener failure (Accept
// returns a non-Temporary error, server.go:950-983), Serve returns that error, but the
// connections already open keep being served (handleRawConn's goroutines run serveStreams;
// Serve's deferred cleanup closes only the listener, server.go:938-945): a call on an
// already-open client connection still runs its handler and succeeds. Two failures: the
// listener closed, and a wrapped listener whose Accept fails with an injected error.
type failingListener struct {
	net.Listener
	fail chan struct{}
}

var errInjected = errors.New("injected accept failure")

func (f *failingListener) Accept() (net.Conn, error) {
	type res struct {
		c   net.Conn
		err error
	}
	rc := make(chan res, 1)
	go func() { c, err := f.Listener.Accept(); rc <- res{c, err} }()
	select {
	case r := <-rc:
		return r.c, r.err
	case <-f.fail:
		return nil, errInjected
	}
}

func TestT5bOpenConnsServedAfterListenerFailure(t *testing.T) {
	for _, mode := range []string{"close", "inject"} {
		t.Run(mode, func(t *testing.T) {
			var runs atomic.Int64
			sd := service("t5b.S", []grpc.MethodDesc{unary("t5b.S", "U",
				func(ctx context.Context, in *msg) (*msg, error) {
					runs.Add(1)
					return in, nil
				})}, nil)
			fl := &failingListener{fail: make(chan struct{})}
			s := serve(t, func(l net.Listener) net.Listener { fl.Listener = l; return fl }, nil, sd)
			cc := dial(t, s.addr)
			if _, err := invoke(cc, ctxT(t, 5*time.Second), "/t5b.S/U", []byte("a")); err != nil {
				t.Fatal(err)
			}
			if mode == "close" {
				fl.Listener.Close()
			} else {
				close(fl.fail)
			}
			select {
			case err := <-s.served:
				if err == nil {
					t.Fatal("Serve returned nil after a listener failure")
				}
				if mode == "inject" && !errors.Is(err, errInjected) {
					t.Fatalf("Serve returned %v, want the injected error", err)
				}
				t.Logf("Serve returned %v", err)
			case <-time.After(10 * time.Second):
				t.Fatal("Serve did not return after the listener failed")
			}
			before := runs.Load()
			for i := 0; i < 5; i++ {
				out, err := invoke(cc, ctxT(t, 5*time.Second), "/t5b.S/U", []byte("b"))
				if err != nil || string(out.Value) != "b" {
					t.Fatalf("call on the open connection after Serve returned: %v %v", out, err)
				}
			}
			if runs.Load()-before != 5 {
				t.Fatalf("handler runs after the failure: %d, want 5", runs.Load()-before)
			}
		})
	}
}

// =============================================================================================
// T6. Scope §7 T6 ("HTTP/2 only"; §2.2: the model is of Serve(lis), grpc's own HTTP/2 transport,
// not ServeHTTP): the examples serve grpc only through gs.Serve(l). The test scans the Go sources
// of this module (examples/, nested modules excluded, test files excluded: the verified programs)
// for every grpc server -- a variable assigned from v3rpc.Server(...) or grpc.NewServer(...) --
// and every method called on it among Serve/ServeHTTP, and asserts the set.
//
// NOTE: the Scope cites only examples/lib/etcdstart/common.go:200; examples/lib/cluster3/
// cluster3.go also serves etcd's grpc server, also by `go gs.Serve(cl)` (same form, so the claim
// holds; the citation is incomplete).
func TestT6ServeOnlyThroughServe(t *testing.T) {
	root, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(root, "go.mod")); err != nil {
		t.Fatalf("examples root not found at %s", root)
	}
	var found []string
	var http []string
	err = filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if p != root {
				if _, err := os.Stat(filepath.Join(p, "go.mod")); err == nil {
					return filepath.SkipDir // a nested module
				}
				if d.Name() == "testdata" || strings.HasPrefix(d.Name(), ".") {
					return filepath.SkipDir
				}
			}
			return nil
		}
		if !strings.HasSuffix(p, ".go") || strings.HasSuffix(p, "_test.go") {
			return nil
		}
		fset, f := parseFile(t, p)
		rel, _ := filepath.Rel(root, p)
		// grpc servers: identifiers assigned from v3rpc.Server(...) or grpc.NewServer(...)
		servers := map[string]bool{}
		ast.Inspect(f, func(n ast.Node) bool {
			as, ok := n.(*ast.AssignStmt)
			if !ok || len(as.Rhs) != 1 {
				return true
			}
			c, ok := as.Rhs[0].(*ast.CallExpr)
			if !ok {
				return true
			}
			if s, ok := c.Fun.(*ast.SelectorExpr); ok {
				if x, ok := s.X.(*ast.Ident); ok &&
					((x.Name == "v3rpc" && s.Sel.Name == "Server") ||
						(x.Name == "grpc" && s.Sel.Name == "NewServer")) {
					if id, ok := as.Lhs[0].(*ast.Ident); ok {
						servers[id.Name] = true
					}
				}
			}
			return true
		})
		ast.Inspect(f, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			s, ok := c.Fun.(*ast.SelectorExpr)
			if !ok {
				return true
			}
			if s.Sel.Name == "ServeHTTP" {
				http = append(http, fmt.Sprintf("%s:%d", rel, fset.Position(c.Pos()).Line))
			}
			if id, ok := s.X.(*ast.Ident); ok && servers[id.Name] &&
				(s.Sel.Name == "Serve" || s.Sel.Name == "ServeHTTP") {
				found = append(found, fmt.Sprintf("%s: %s.%s", rel, id.Name, s.Sel.Name))
			}
			return true
		})
		// a grpc server used as an http.Handler (passed to http.Serve/ListenAndServe/Handle)
		ast.Inspect(f, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			for _, a := range c.Args {
				if id, ok := a.(*ast.Ident); ok && servers[id.Name] {
					http = append(http, fmt.Sprintf("%s:%d (server passed as an argument)", rel,
						fset.Position(c.Pos()).Line))
				}
			}
			return true
		})
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	sort.Strings(found)
	t.Logf("grpc servers served: %v", found)
	want := []string{"lib/cluster3/cluster3.go: gs.Serve", "lib/etcdstart/common.go: gs.Serve"}
	if !reflect.DeepEqual(found, want) {
		t.Fatalf("grpc servers served: %v, want %v", found, want)
	}
	if len(http) != 0 {
		t.Fatalf("ServeHTTP or a grpc server as an argument: %v", http)
	}
}

// =============================================================================================
// T7. Scope §7 T7 ("the lend; one lgMu reader"): in the pinned etcd (v3rpc/interceptor.go),
// newLogUnaryInterceptor calls s.Logger() exactly once, in a statement after the one calling
// handler(ctx, req); and the quota check runs inside the handler: v3rpc.Server registers
// NewQuotaKVServer and NewQuotaLeaseServer (grpc.go), whose Put, Txn and LeaseGrant start with
// s.qa.check (quota.go), and no interceptor of interceptor.go references the quota. Source
// inspection of the module cache's copy (go list -m), by Go's AST.
func TestT7LogAfterHandlerQuotaInHandler(t *testing.T) {
	dir := filepath.Join(modDir(t, "go.etcd.io/etcd/server/v3"), "etcdserver", "api", "v3rpc")
	_, ic := parseFile(t, filepath.Join(dir, "interceptor.go"))
	fd := funcDecl(ic, "", "newLogUnaryInterceptor")
	if fd == nil {
		t.Fatal("newLogUnaryInterceptor not found")
	}
	var lit *ast.FuncLit
	for _, st := range fd.Body.List {
		if r, ok := st.(*ast.ReturnStmt); ok && len(r.Results) == 1 {
			lit, _ = r.Results[0].(*ast.FuncLit)
		}
	}
	if lit == nil {
		t.Fatal("newLogUnaryInterceptor does not return a function literal")
	}
	isHandler := func(n ast.Node) bool {
		c, ok := n.(*ast.CallExpr)
		if !ok {
			return false
		}
		id, ok := c.Fun.(*ast.Ident)
		return ok && id.Name == "handler"
	}
	isLogger := func(n ast.Node) bool { return selCall(n, "s", "Logger") }
	if k := countIn(lit, isLogger); k != 1 {
		t.Fatalf("s.Logger() called %d times in the interceptor, want 1", k)
	}
	if k := countIn(lit, isHandler); k != 1 {
		t.Fatalf("handler called %d times in the interceptor, want 1", k)
	}
	hi, li := -1, -1
	for i, st := range lit.Body.List {
		if contains(st, isHandler) {
			hi = i
		}
		if contains(st, isLogger) {
			li = i
		}
	}
	if hi < 0 || li < 0 || !(hi < li) || contains(lit.Body.List[li], isHandler) {
		t.Fatalf("handler at statement %d, s.Logger() at statement %d: Logger is not after handler",
			hi, li)
	}
	// no interceptor in interceptor.go touches the quota
	quotaRef := func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		return ok && (strings.Contains(strings.ToLower(id.Name), "quota") || id.Name == "qa")
	}
	if contains(ic, quotaRef) {
		t.Fatal("interceptor.go references the quota")
	}
	// grpc.go registers the quota servers
	_, gf := parseFile(t, filepath.Join(dir, "grpc.go"))
	srv := funcDecl(gf, "", "Server")
	for _, reg := range [][2]string{{"RegisterKVServer", "NewQuotaKVServer"},
		{"RegisterLeaseServer", "NewQuotaLeaseServer"}} {
		ok := contains(srv, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok || !selCall(c, "pb", reg[0]) || len(c.Args) != 2 {
				return false
			}
			a, ok := c.Args[1].(*ast.CallExpr)
			if !ok {
				return false
			}
			id, ok := a.Fun.(*ast.Ident)
			return ok && id.Name == reg[1]
		})
		if !ok {
			t.Fatalf("v3rpc.Server does not call pb.%s(_, %s(s))", reg[0], reg[1])
		}
	}
	// the quota servers' handlers check first
	_, qf := parseFile(t, filepath.Join(dir, "quota.go"))
	for _, m := range [][2]string{{"quotaKVServer", "Put"}, {"quotaKVServer", "Txn"},
		{"quotaLeaseServer", "LeaseGrant"}} {
		fd := funcDecl(qf, m[0], m[1])
		if fd == nil || len(fd.Body.List) == 0 {
			t.Fatalf("%s.%s not found", m[0], m[1])
		}
		first := fd.Body.List[0]
		if !contains(first, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok {
				return false
			}
			s, ok := c.Fun.(*ast.SelectorExpr)
			if !ok || s.Sel.Name != "check" {
				return false
			}
			inner, ok := s.X.(*ast.SelectorExpr)
			return ok && inner.Sel.Name == "qa"
		}) {
			t.Fatalf("%s.%s does not start with s.qa.check", m[0], m[1])
		}
	}
}

// =============================================================================================
// T8. Scope §7 T8 ("one deposit, one run (M4)"; §2.2 "The pair", (a)-(b)): under etcd's client
// dial configuration -- no service-config retry policy (clientv3's resolver gives only
// {"loadBalancingPolicy": "round_robin"}, client/v3/internal/resolver/resolver.go:44) -- a
// processed attempt that fails with UNAVAILABLE is not resent by grpc: the handler runs once per
// Invoke. Two clients: clientv3.New's own connection (cli.ActiveConnection(), with clientv3's
// interceptors; a custom method is "nonRepeatable" under its retry interceptor, which retries
// such an UNAVAILABLE only for "repeatable" calls such as Range, each retry a new Invoke, i.e. a
// new deposit), and a plain grpc.NewClient with no service config.
func TestT8UnavailableRunsOnce(t *testing.T) {
	var runs atomic.Int64
	sd := service("t8.S", []grpc.MethodDesc{unary("t8.S", "U",
		func(ctx context.Context, in *msg) (*msg, error) {
			runs.Add(1)
			return nil, status.Error(codes.Unavailable, "t8: handler says unavailable")
		})}, nil)
	s := serve(t, nil, nil, sd)
	check := func(t *testing.T, cc *grpc.ClientConn) {
		for i := 0; i < 5; i++ {
			before := runs.Load()
			_, err := invoke(cc, ctxT(t, 5*time.Second), "/t8.S/U", nil)
			wantCode(t, "Invoke", err, codes.Unavailable)
			time.Sleep(50 * time.Millisecond) // a retry would have run by now
			if got := runs.Load() - before; got != 1 {
				t.Fatalf("handler ran %d times for one Invoke", got)
			}
		}
	}
	t.Run("clientv3", func(t *testing.T) {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{s.addr},
			DialTimeout: etcdstart.DialTimeout, DialKeepAliveTime: etcdstart.KeepAliveTime,
			DialKeepAliveTimeout: etcdstart.KeepAliveTimeout, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		defer cli.Close()
		check(t, cli.ActiveConnection())
	})
	t.Run("grpc.NewClient", func(t *testing.T) { check(t, dial(t, s.addr)) })
}

// T8b. Scope §7 T8b (counter-test: why grpcResolverAt's bound is cited): with a service-config
// retry policy retrying UNAVAILABLE (maxAttempts 3), grpc resends the processed attempt
// (stream.go's retry, shouldRetry/retryLocked): the same handler runs 3 times for one Invoke.
// So "one deposit, one run" needs the clients' dial configuration.
func TestT8bRetryPolicyRerunsHandler(t *testing.T) {
	var runs atomic.Int64
	sd := service("t8b.S", []grpc.MethodDesc{unary("t8b.S", "U",
		func(ctx context.Context, in *msg) (*msg, error) {
			runs.Add(1)
			return nil, status.Error(codes.Unavailable, "t8b: handler says unavailable")
		})}, nil)
	s := serve(t, nil, nil, sd)
	cc := dial(t, s.addr, grpc.WithDefaultServiceConfig(`{"methodConfig": [{
		"name": [{"service": "t8b.S"}],
		"retryPolicy": {"maxAttempts": 3, "initialBackoff": "0.01s", "maxBackoff": "0.05s",
			"backoffMultiplier": 1.0, "retryableStatusCodes": ["UNAVAILABLE"]}}]}`))
	_, err := invoke(cc, ctxT(t, 10*time.Second), "/t8b.S/U", nil)
	wantCode(t, "Invoke", err, codes.Unavailable)
	if got := runs.Load(); got != 3 {
		t.Fatalf("handler ran %d times for one Invoke under a retry policy, want 3", got)
	}
}

// =============================================================================================
// T9. Scope §7 T9 ("acceptRun's dispatch, its bounds (m4)"): an unregistered method (unknown
// service, unknown method of a known service, a malformed name) is answered Unimplemented and
// runs no handler (server.go:1562-1570, :1599-1614: no unknownStreamDesc). And etcd's server has
// no UnknownServiceHandler (server.go:568-580 sets unknownStreamDesc) and no stream wrapper
// (server.go:666-672, xDS-internal, used at :1434-1436): checked on a real etcd server built as
// the examples build it (its opts by reflection: unknownStreamDesc and streamWrapper nil,
// and an unregistered call answered Unimplemented), and by source: the grpc option
// constructors the specs cover (Spec/google_golang_org/grpc/: CustomCodec, ChainUnaryInterceptor,
// ChainStreamInterceptor, MaxRecvMsgSize, MaxSendMsgSize, MaxConcurrentStreams,
// KeepaliveEnforcementPolicy, StatsHandler) set neither field nor numServerWorkers, and
// v3rpc.Server (grpc.go) builds its options only from those (plus Creds under TLS, which the
// examples do not use).
func TestT9Unimplemented(t *testing.T) {
	t.Run("plain", func(t *testing.T) {
		var runs atomic.Int64
		h := func(ctx context.Context, in *msg) (*msg, error) { runs.Add(1); return in, nil }
		sd := service("t9.S", []grpc.MethodDesc{unary("t9.S", "U", h)},
			[]grpc.StreamDesc{stream("St", func(any, grpc.ServerStream) error { runs.Add(1); return nil })})
		s := serve(t, nil, nil, sd)
		cc := dial(t, s.addr)
		for _, m := range []string{"/t9.S/Nope", "/t9.X/U", "/t9.S", "t9.S/U", "/t9.S/U/"} {
			_, err := invoke(cc, ctxT(t, 5*time.Second), m, nil)
			wantCode(t, m, err, codes.Unimplemented)
		}
		if runs.Load() != 0 {
			t.Fatalf("%d handler runs for unregistered methods", runs.Load())
		}
		if _, err := invoke(cc, ctxT(t, 5*time.Second), "/t9.S/U", nil); err != nil || runs.Load() != 1 {
			t.Fatalf("registered method: %v, runs %d", err, runs.Load())
		}
	})
	t.Run("etcd", func(t *testing.T) {
		gs, addr := startEtcd(t, "t9")
		o := srvOpts(gs)
		if !o.FieldByName("unknownStreamDesc").IsNil() {
			t.Fatal("etcd's grpc server has an UnknownServiceHandler")
		}
		if !o.FieldByName("streamWrapper").IsNil() {
			t.Fatal("etcd's grpc server has a stream wrapper")
		}
		cc := dial(t, addr)
		for _, m := range []string{"/etcdserverpb.KV/Nope", "/nope.S/Range"} {
			_, err := invoke(cc, ctxT(t, 5*time.Second), m, nil)
			wantCode(t, m, err, codes.Unimplemented)
		}
	})
	t.Run("source", func(t *testing.T) {
		gdir := modDir(t, "google.golang.org/grpc")
		_, sf := parseFile(t, filepath.Join(gdir, "server.go"))
		forbidden := map[string]bool{"unknownStreamDesc": true, "streamWrapper": true,
			"numServerWorkers": true}
		specified := []string{"CustomCodec", "ChainUnaryInterceptor", "ChainStreamInterceptor",
			"MaxRecvMsgSize", "MaxSendMsgSize", "MaxConcurrentStreams",
			"KeepaliveEnforcementPolicy", "StatsHandler"}
		for _, name := range specified {
			fd := funcDecl(sf, "", name)
			if fd == nil {
				t.Fatalf("grpc.%s not found", name)
			}
			ast.Inspect(fd, func(n ast.Node) bool {
				if s, ok := n.(*ast.SelectorExpr); ok && forbidden[s.Sel.Name] {
					t.Errorf("grpc.%s touches %s", name, s.Sel.Name)
				}
				return true
			})
		}
		// the positive control: the options that do set them
		for name, field := range map[string]string{"UnknownServiceHandler": "unknownStreamDesc",
			"NumStreamWorkers": "numServerWorkers", "xdsFilterWrapperOption": "streamWrapper"} {
			fd := funcDecl(sf, "", name)
			if fd == nil || !contains(fd, func(n ast.Node) bool {
				s, ok := n.(*ast.SelectorExpr)
				return ok && s.Sel.Name == field
			}) {
				t.Fatalf("control: grpc.%s does not set %s", name, field)
			}
		}
		// v3rpc.Server's options: only grpc.<specified>, grpc.Creds, and the caller's gopts
		edir := filepath.Join(modDir(t, "go.etcd.io/etcd/server/v3"), "etcdserver", "api", "v3rpc")
		_, gf := parseFile(t, filepath.Join(edir, "grpc.go"))
		srv := funcDecl(gf, "", "Server")
		ok := map[string]bool{"Creds": true, "NewServer": true}
		for _, n := range specified {
			ok[n] = true
		}
		var used []string
		ast.Inspect(srv, func(n ast.Node) bool {
			c, isCall := n.(*ast.CallExpr)
			if !isCall {
				return true
			}
			if s, isSel := c.Fun.(*ast.SelectorExpr); isSel {
				if x, isId := s.X.(*ast.Ident); isId && x.Name == "grpc" {
					used = append(used, s.Sel.Name)
					if !ok[s.Sel.Name] {
						t.Errorf("v3rpc.Server calls grpc.%s", s.Sel.Name)
					}
				}
			}
			return true
		})
		t.Logf("v3rpc.Server calls grpc.%v", used)
		if strings.Contains(fmt.Sprint(used), "UnknownServiceHandler") {
			t.Fatal("v3rpc.Server sets an UnknownServiceHandler")
		}
	})
}

// =============================================================================================
// T9b. Scope §7 T9b ("joint Nodup (M1)"; §2.2 acceptRun: the path split at its LAST '/',
// server.go:1566-1572, then s.services[svc].streams[m], :1592-1597): service "a" with a unary
// method "b/c" (handler A) and service "a/b" with a stream "c" (handler B) both register on one
// server without a fatal error (register checks only the service name's uniqueness,
// server.go:796-798), and a call to "/a/b/c" runs B (service "a/b", method "c"), never A: an
// entry whose method part holds a '/' is never dispatched to.
//
// NOTE (side finding, not a Scope claim): within one service, a unary method and a stream of the
// same name also register without a fatal error -- in v1.84 both go into one map, the methods
// after the streams (server.go:804-816), so the unary method silently wins and the stream is
// never dispatched to. Proof/google_golang_org/grpc/InvGrpcServer.lean's header says
// RegisterService needs "its method and stream names distinct: grpc's logger.Fatalf otherwise":
// the premise is stronger than Go needs (sound), but its stated reason is false.
func TestT9bSlashCollision(t *testing.T) {
	var a, bRuns atomic.Int64
	sdA := service("a", []grpc.MethodDesc{unary("a", "b/c", func(ctx context.Context, in *msg) (*msg, error) {
		a.Add(1)
		return &msg{Value: []byte("A")}, nil
	})}, nil)
	sdB := service("a/b", nil, []grpc.StreamDesc{stream("c", func(srv any, ss grpc.ServerStream) error {
		bRuns.Add(1)
		in := new(msg)
		if err := ss.RecvMsg(in); err != nil {
			return err
		}
		return ss.SendMsg(&msg{Value: []byte("B")})
	})})
	s := serve(t, nil, nil, sdA, sdB) // a logger.Fatalf would exit the test binary here
	cc := dial(t, s.addr)
	out, err := invoke(cc, ctxT(t, 5*time.Second), "/a/b/c", nil)
	if err != nil || string(out.Value) != "B" {
		t.Fatalf("/a/b/c: %v %v", out, err)
	}
	cs, err := cc.NewStream(ctxT(t, 5*time.Second), &grpc.StreamDesc{ServerStreams: true,
		ClientStreams: true}, "/a/b/c")
	if err != nil {
		t.Fatal(err)
	}
	if err := cs.SendMsg(&msg{}); err != nil {
		t.Fatal(err)
	}
	out = new(msg)
	if err := cs.RecvMsg(out); err != nil || string(out.Value) != "B" {
		t.Fatalf("stream /a/b/c: %v %v", out, err)
	}
	if a.Load() != 0 || bRuns.Load() != 2 {
		t.Fatalf("runs: A %d, B %d; want A 0, B 2", a.Load(), bRuns.Load())
	}
	si := s.gs.GetServiceInfo()
	if _, ok := si["a"]; !ok {
		t.Fatal("service a not registered")
	}
	if _, ok := si["a/b"]; !ok {
		t.Fatal("service a/b not registered")
	}

	t.Run("same name in one service (NOTE)", func(t *testing.T) {
		var u, st atomic.Int64
		sd := service("t9b.S", []grpc.MethodDesc{unary("t9b.S", "M", func(ctx context.Context, in *msg) (*msg, error) {
			u.Add(1)
			return &msg{Value: []byte("unary")}, nil
		})}, []grpc.StreamDesc{stream("M", func(srv any, ss grpc.ServerStream) error {
			st.Add(1)
			return ss.SendMsg(&msg{Value: []byte("stream")})
		})})
		s := serve(t, nil, nil, sd) // no logger.Fatalf
		cc := dial(t, s.addr)
		out, err := invoke(cc, ctxT(t, 5*time.Second), "/t9b.S/M", nil)
		if err != nil || string(out.Value) != "unary" || u.Load() != 1 || st.Load() != 0 {
			t.Fatalf("got %v %v, unary runs %d, stream runs %d", out, err, u.Load(), st.Load())
		}
	})
}

// =============================================================================================
// T10. Scope §7 T10 (acceptRun's composite: grpcAccepted's Go facts, grpcSrvStreamChain (M3)):
// (1) the handler sees the client's outgoing metadata as its incoming metadata (unary and
// stream); (2) the unary chain runs in registration order (chainUnaryServerInterceptors,
// server.go:1207-1240); (3) with no stream interceptor the stream handler is called directly by
// processRPC (server.go:1446-1450) on grpc's own *serverStream, and with several
// (ChainStreamInterceptor, twice) they run in order (server.go:1243-1275, :1451-1457) with
// info.FullMethod the full name, and a unary call skips the stream chain (:1446); (4) the handler
// registered under the full name runs (two services with a method of the same name).
func TestT10Composite(t *testing.T) {
	var mu sync.Mutex
	var trace []string
	log := func(s string) { mu.Lock(); trace = append(trace, s); mu.Unlock() }
	take := func() []string { mu.Lock(); defer mu.Unlock(); r := trace; trace = nil; return r }
	ui := func(name string) grpc.UnaryServerInterceptor {
		return func(ctx context.Context, req any, info *grpc.UnaryServerInfo, h grpc.UnaryHandler) (any, error) {
			log(name)
			return h(ctx, req)
		}
	}
	si := func(name string) grpc.StreamServerInterceptor {
		return func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo, h grpc.StreamHandler) error {
			log(name + ":" + info.FullMethod)
			return h(srv, ss)
		}
	}
	var gotMD sync.Map
	mdOf := func(ctx context.Context) string {
		md, _ := metadata.FromIncomingContext(ctx)
		return strings.Join(md.Get("x-t10"), ",")
	}
	var directCaller, streamType atomic.Value
	mk := func(svc string) *grpc.ServiceDesc {
		return service(svc, []grpc.MethodDesc{unary(svc, "U", func(ctx context.Context, in *msg) (*msg, error) {
			log("handler " + svc + "/U")
			gotMD.Store(svc+"/U", mdOf(ctx))
			return &msg{Value: []byte(svc)}, nil
		})}, []grpc.StreamDesc{stream("St", func(srv any, ss grpc.ServerStream) error {
			log("handler " + svc + "/St")
			gotMD.Store(svc+"/St", mdOf(ss.Context()))
			pc := make([]uintptr, 2)
			runtime.Callers(1, pc) // [this handler, its caller]
			fr := runtime.CallersFrames(pc)
			fr.Next()
			caller, _ := fr.Next()
			directCaller.Store(caller.Function)
			streamType.Store(reflect.TypeOf(ss).String())
			return ss.SendMsg(&msg{Value: []byte(svc)})
		})})
	}
	callStream := func(t *testing.T, cc *grpc.ClientConn, ctx context.Context, m string) string {
		cs, err := cc.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, m)
		if err != nil {
			t.Fatal(err)
		}
		cs.CloseSend()
		out := new(msg)
		if err := cs.RecvMsg(out); err != nil {
			t.Fatal(err)
		}
		return string(out.Value)
	}

	t.Run("no stream interceptor", func(t *testing.T) {
		s := serve(t, nil, nil, mk("t10.P"), mk("t10.Q"))
		cc := dial(t, s.addr)
		ctx := metadata.AppendToOutgoingContext(ctxT(t, 5*time.Second), "x-t10", "v1", "x-t10", "v2")
		if v := callStream(t, cc, ctx, "/t10.Q/St"); v != "t10.Q" {
			t.Fatalf("stream /t10.Q/St ran %s's handler", v)
		}
		if c := directCaller.Load().(string); c != "google.golang.org/grpc.(*Server).processRPC" {
			t.Fatalf("stream handler called by %s, want processRPC directly", c)
		}
		if ty := streamType.Load().(string); ty != "*grpc.serverStream" {
			t.Fatalf("stream handler got a %s, want grpc's *grpc.serverStream", ty)
		}
		if md, _ := gotMD.Load("t10.Q/St"); md != "v1,v2" {
			t.Fatalf("stream handler's incoming metadata x-t10 = %q", md)
		}
		take()
	})

	t.Run("chains", func(t *testing.T) {
		s := serve(t, nil, []grpc.ServerOption{
			grpc.ChainUnaryInterceptor(ui("u1"), ui("u2")), grpc.ChainUnaryInterceptor(ui("u3")),
			grpc.ChainStreamInterceptor(si("s1"), si("s2")), grpc.ChainStreamInterceptor(si("s3")),
		}, mk("t10.P"), mk("t10.Q"))
		cc := dial(t, s.addr)
		ctx := metadata.AppendToOutgoingContext(ctxT(t, 5*time.Second), "x-t10", "m")
		take()
		out, err := invoke(cc, ctx, "/t10.P/U", nil)
		if err != nil || string(out.Value) != "t10.P" {
			t.Fatalf("/t10.P/U: %v %v", out, err)
		}
		if got, want := take(), []string{"u1", "u2", "u3", "handler t10.P/U"}; !reflect.DeepEqual(got, want) {
			t.Fatalf("unary order %v, want %v (and no stream interceptor)", got, want)
		}
		if md, _ := gotMD.Load("t10.P/U"); md != "m" {
			t.Fatalf("unary handler's incoming metadata x-t10 = %q", md)
		}
		out, err = invoke(cc, ctx, "/t10.Q/U", nil)
		if err != nil || string(out.Value) != "t10.Q" {
			t.Fatalf("/t10.Q/U ran %v %v", out, err)
		}
		take()
		if v := callStream(t, cc, ctx, "/t10.P/St"); v != "t10.P" {
			t.Fatalf("stream /t10.P/St ran %s's handler", v)
		}
		want := []string{"s1:/t10.P/St", "s2:/t10.P/St", "s3:/t10.P/St", "handler t10.P/St"}
		if got := take(); !reflect.DeepEqual(got, want) {
			t.Fatalf("stream order %v, want %v", got, want)
		}
		if md, _ := gotMD.Load("t10.P/St"); md != "m" {
			t.Fatalf("stream handler's incoming metadata x-t10 = %q", md)
		}
	})
}

// T10b. Review B2 of CP1a (acceptRun's composite, the model's stream arm): grpc calls a stream
// descriptor's handler directly, skipping a configured stream interceptor, when the descriptor sets
// neither ClientStreams nor ServerStreams (processRPC, server.go:1446-1450), so the model (which
// calls the interceptor whenever there is one) is faithful only for flagged stream descriptors:
// RegisterService's premise (B1b) requires a flag on every stream descriptor. Also checks that
// every stream descriptor etcd registers (Watch, Lease's LeaseKeepAlive, Maintenance's Snapshot,
// grpc's health Watch) sets one.
func TestT10bUnflaggedStreamSkipsInterceptor(t *testing.T) {
	var icptRuns atomic.Int64
	var directCaller atomic.Value
	si := func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo, h grpc.StreamHandler) error {
		icptRuns.Add(1)
		return h(srv, ss)
	}
	h := func(srv any, ss grpc.ServerStream) error {
		pc := make([]uintptr, 2)
		runtime.Callers(1, pc) // [this handler, its caller]
		fr := runtime.CallersFrames(pc)
		fr.Next()
		caller, _ := fr.Next()
		directCaller.Store(caller.Function)
		return ss.SendMsg(&msg{Value: []byte("ok")})
	}
	unflagged := grpc.StreamDesc{StreamName: "St", Handler: h}
	s := serve(t, nil, []grpc.ServerOption{grpc.ChainStreamInterceptor(si)},
		service("t10b.S", nil, []grpc.StreamDesc{unflagged}))
	cc := dial(t, s.addr)
	cs, err := cc.NewStream(ctxT(t, 5*time.Second), &grpc.StreamDesc{ServerStreams: true,
		ClientStreams: true}, "/t10b.S/St")
	if err != nil {
		t.Fatal(err)
	}
	cs.CloseSend()
	out := new(msg)
	if err := cs.RecvMsg(out); err != nil || string(out.Value) != "ok" {
		t.Fatalf("unflagged stream: %v %v", out, err)
	}
	if n := icptRuns.Load(); n != 0 {
		t.Fatalf("stream interceptor ran %d times for an unflagged descriptor, want 0", n)
	}
	if c := directCaller.Load().(string); c != "google.golang.org/grpc.(*Server).processRPC" {
		t.Fatalf("unflagged stream handler called by %s, want processRPC directly", c)
	}

	// etcd's stream descriptors all set a flag.
	for _, sd := range []*grpc.ServiceDesc{&pb.Watch_ServiceDesc, &pb.Lease_ServiceDesc,
		&pb.Maintenance_ServiceDesc, &pb.KV_ServiceDesc, &pb.Cluster_ServiceDesc, &pb.Auth_ServiceDesc,
		&healthpb.Health_ServiceDesc} {
		for _, st := range sd.Streams {
			if !st.ClientStreams && !st.ServerStreams {
				t.Fatalf("%s/%s sets no stream flag", sd.ServiceName, st.StreamName)
			}
		}
	}
	if n := len(pb.Watch_ServiceDesc.Streams) + len(pb.Lease_ServiceDesc.Streams) +
		len(pb.Maintenance_ServiceDesc.Streams) + len(healthpb.Health_ServiceDesc.Streams); n != 4 {
		t.Fatalf("etcd's stream descriptors: %d, want 4 (Watch, LeaseKeepAlive, Snapshot, health Watch)", n)
	}
}

// =============================================================================================
// T11. Scope §7 T11 (respond's composite, §2.2): a reply above MaxSendMsgSize fails at the client
// with ResourceExhausted, and the server does not panic and goes on serving (wrapUnaryHandler's
// stream.SendMsg, server.go:1281-1289, returns the size error, which processRPC writes as the
// status, :1458-1465); the same for a stream handler's SendMsg; and a handler error built with
// status.Error(code, desc) reaches the client with the same code and description.
func TestT11Respond(t *testing.T) {
	const limit = 1024
	big := bytes.Repeat([]byte("x"), 4*limit)
	var streamSendErr atomic.Value
	sd := service("t11.S", []grpc.MethodDesc{
		unary("t11.S", "Big", func(ctx context.Context, in *msg) (*msg, error) { return &msg{Value: big}, nil }),
		unary("t11.S", "Small", func(ctx context.Context, in *msg) (*msg, error) { return in, nil }),
		unary("t11.S", "Err", func(ctx context.Context, in *msg) (*msg, error) {
			return nil, status.Error(codes.FailedPrecondition, "etcdserver: t11 description")
		}),
	}, []grpc.StreamDesc{stream("BigSt", func(srv any, ss grpc.ServerStream) error {
		err := ss.SendMsg(&msg{Value: big})
		streamSendErr.Store(fmt.Sprint(status.Code(err)))
		return err
	})})
	s := serve(t, nil, []grpc.ServerOption{grpc.MaxSendMsgSize(limit)}, sd)
	cc := dial(t, s.addr)
	_, err := invoke(cc, ctxT(t, 5*time.Second), "/t11.S/Big", nil)
	wantCode(t, "Big", err, codes.ResourceExhausted)
	t.Logf("Big: %v", err)
	cs, err := cc.NewStream(ctxT(t, 5*time.Second), &grpc.StreamDesc{ServerStreams: true,
		ClientStreams: true}, "/t11.S/BigSt")
	if err != nil {
		t.Fatal(err)
	}
	cs.CloseSend()
	wantCode(t, "BigSt", cs.RecvMsg(new(msg)), codes.ResourceExhausted)
	if c := streamSendErr.Load(); c != codes.ResourceExhausted.String() {
		t.Fatalf("the stream handler's SendMsg error code: %v", c)
	}
	out, err := invoke(cc, ctxT(t, 5*time.Second), "/t11.S/Small", []byte("ok"))
	if err != nil || string(out.Value) != "ok" {
		t.Fatalf("server not serving after the oversize reply: %v %v", out, err)
	}
	_, err = invoke(cc, ctxT(t, 5*time.Second), "/t11.S/Err", nil)
	st, _ := status.FromError(err)
	if st.Code() != codes.FailedPrecondition || st.Message() != "etcdserver: t11 description" {
		t.Fatalf("handler error reached the client as %v / %q", st.Code(), st.Message())
	}
}

// =============================================================================================
// T12. Scope §7 T12 (finishStream's composite, §2.2): a stream handler's status error reaches the
// client with its code and description; a handler error that is not a status error goes through
// processRPC's `status.FromError` (status/status.go:96-127: ok=false for an error with no
// GRPCStatus) and then `status.FromContextError` (server.go:1459-1464; status/status.go:151-162,
// errors.Is), so fmt.Errorf("...%w", context.Canceled) reaches the client as Canceled and a
// wrapped context.DeadlineExceeded as DeadlineExceeded, with the error's text as the description;
// any other plain error as Unknown. Real behavior, as asserted: the same for unary handlers (in
// v1.84 a unary call goes through the same processRPC, wrapUnaryHandler, server.go:1281).
func TestT12FinishStream(t *testing.T) {
	cases := []struct {
		name string
		err  error
		code codes.Code
		desc string
	}{
		{"status", status.Error(codes.Aborted, "t12 aborted"), codes.Aborted, "t12 aborted"},
		{"canceled", fmt.Errorf("t12 wrap: %w", context.Canceled), codes.Canceled, "t12 wrap: context canceled"},
		{"deadline", fmt.Errorf("t12 wrap: %w", context.DeadlineExceeded), codes.DeadlineExceeded,
			"t12 wrap: context deadline exceeded"},
		{"plain", errors.New("t12 plain"), codes.Unknown, "t12 plain"},
		{"wrapped status", fmt.Errorf("t12 outer: %w", status.Error(codes.NotFound, "inner")),
			codes.NotFound, "t12 outer: rpc error: code = NotFound desc = inner"},
	}
	var ms []grpc.MethodDesc
	var ss []grpc.StreamDesc
	for _, c := range cases {
		e := c.err
		ms = append(ms, unary("t12.S", "U"+c.name, func(context.Context, *msg) (*msg, error) { return nil, e }))
		ss = append(ss, stream("S"+c.name, func(any, grpc.ServerStream) error { return e }))
	}
	s := serve(t, nil, nil, service("t12.S", ms, ss))
	cc := dial(t, s.addr)
	for _, c := range cases {
		cs, err := cc.NewStream(ctxT(t, 5*time.Second), &grpc.StreamDesc{ServerStreams: true,
			ClientStreams: true}, "/t12.S/S"+c.name)
		if err != nil {
			t.Fatal(err)
		}
		cs.CloseSend()
		err = cs.RecvMsg(new(msg))
		st, _ := status.FromError(err)
		if st.Code() != c.code || st.Message() != c.desc {
			t.Errorf("stream %s: client got %v / %q, want %v / %q", c.name, st.Code(), st.Message(),
				c.code, c.desc)
		}
		_, err = invoke(cc, ctxT(t, 5*time.Second), "/t12.S/U"+c.name, nil)
		st, _ = status.FromError(err)
		if st.Code() != c.code || st.Message() != c.desc {
			t.Errorf("unary %s: client got %v / %q, want %v / %q", c.name, st.Code(), st.Message(),
				c.code, c.desc)
		}
	}
}
