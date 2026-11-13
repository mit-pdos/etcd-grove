package lease

import (
	"context"
	"net"
	"net/http"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// sweepPanicTraceCtx: every method is the inner *cancelCtx's (so isContext's clauses hold), except
// Value at net/http's httptrace key, which panics.
type sweepPanicTraceCtx struct{ context.Context }

func (c sweepPanicTraceCtx) Value(k any) any {
	// httptrace's key type is unexported; recognise it by its type name.
	if s := typeName(k); s == "httptrace.clientEventContextKey" {
		panic("Value(httptrace key)")
	}
	return c.Context.Value(k)
}

func typeName(k any) string {
	return fmtType(k)
}

// TestLeaseTimeToLiveFollowerValuePanics (k8s 7f-4, Addendum T-h6; etcd-grove-81's context-key sweep):
// a follower's LeaseTimeToLive forwards over HTTP (WithTimeout(ctx), TimeToLiveHTTP), and net/http's
// Transport.roundTrip reads Value at httptrace's key, which panics here although the context meets
// isContext. notes/leasetimetolive-value-refuted.md.
func TestLeaseTimeToLiveFollowerValuePanics(t *testing.T) {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	peers := []string{"127.0.0.1:24951", "127.0.0.1:24952", "127.0.0.1:24953"}
	clients := []string{"127.0.0.1:24956", "127.0.0.1:24957", "127.0.0.1:24958"}
	names := []string{"ctxsweep-1", "ctxsweep-2", "ctxsweep-3"}
	cluster := types.URLsMap{}
	for i, p := range peers {
		cluster[names[i]] = types.URLs{{Scheme: "http", Host: p}}
	}
	srvs := make([]*etcdserver.EtcdServer, 3)
	for i := range peers {
		s, err := etcdstart.BuildServer(names[i], cluster[names[i]], clients[i], cluster, "ctxsweep",
			etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
		if err != nil {
			t.Fatal(err)
		}
		l, err := net.Listen("tcp", peers[i])
		if err != nil {
			t.Fatal(err)
		}
		mux := http.NewServeMux()
		mux.Handle("/", s.RaftHandler())
		mux.Handle(leasehttp.LeasePrefix, s.LeaseHandler())
		mux.Handle(leasehttp.LeaseInternalPrefix, s.LeaseHandler())
		go http.Serve(l, mux)
		srvs[i] = s
	}
	for _, s := range srvs {
		s.Start()
		defer s.Stop()
	}
	// wait for a leader
	var f *etcdserver.EtcdServer
	for d := time.Now().Add(20 * time.Second); time.Now().Before(d) && f == nil; time.Sleep(50 * time.Millisecond) {
		for _, s := range srvs {
			if s.Leader() != 0 && s.Leader() != s.MemberID() {
				f = s
				break
			}
		}
	}
	if f == nil {
		t.Fatal("no follower with a leader")
	}
	inner, cancel := context.WithCancel(context.Background())
	defer cancel()
	// sanity: the plain context gets an answer (or a lease error), no panic
	if _, err := f.LeaseTimeToLive(inner, &pb.LeaseTimeToLiveRequest{ID: 1}); err != nil {
		t.Logf("plain context: err %v (expected ErrLeaseNotFound)", err)
	}
	panicked := func() (r any) {
		defer func() { r = recover() }()
		f.LeaseTimeToLive(sweepPanicTraceCtx{inner}, &pb.LeaseTimeToLiveRequest{ID: 1})
		return nil
	}()
	if panicked == nil {
		t.Fatal("follower's LeaseTimeToLive did not panic")
	}
	t.Logf("recovered: %v", panicked)
}

// causeBadErr (k8s 7f-4, Addendum T-k): an error whose Is panics, used as a context's cause.
type causeBadErr struct{}

func (causeBadErr) Error() string { return "bad cause" }
func (causeBadErr) Is(error) bool { panic("causeBadErr.Is called") }

// TestLeaseTimeToLiveFollowerCausePanics (k8s 7f-4, Addendum T-k; the T-j review's MAJ-1, extended to
// leaseTimeToLive): a follower's LeaseTimeToLive forwards over HTTP (WithTimeout(ctx), then
// TimeToLiveHTTP(cctx) to the leader), and net/http's transport returns context.Cause of the request's
// context once it is done (go1.27.3 net/http/transport.go:698), wrapped in a *url.Error. With
// ctx = context.WithDeadlineCause(Background(), soon, causeBadErr{}) (Perennial's WithDeadlineCause spec
// gives isContext of it, and netCtxOk holds), the deadline fires while the leader's lease handler
// blocks; leaseTimeToLive then calls errors.Is(err, lease.ErrLeaseNotFound) on that error, which calls
// causeBadErr.Is: a panic inside the axiomatized leaseTimeToLive.
func TestLeaseTimeToLiveFollowerCausePanics(t *testing.T) {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	peers := []string{"127.0.0.1:24961", "127.0.0.1:24962", "127.0.0.1:24963"}
	clients := []string{"127.0.0.1:24966", "127.0.0.1:24967", "127.0.0.1:24968"}
	names := []string{"ctxcause-1", "ctxcause-2", "ctxcause-3"}
	cluster := types.URLsMap{}
	for i, p := range peers {
		cluster[names[i]] = types.URLs{{Scheme: "http", Host: p}}
	}
	var block atomic.Bool
	srvs := make([]*etcdserver.EtcdServer, 3)
	for i := range peers {
		s, err := etcdstart.BuildServer(names[i], cluster[names[i]], clients[i], cluster, "ctxcause",
			etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
		if err != nil {
			t.Fatal(err)
		}
		l, err := net.Listen("tcp", peers[i])
		if err != nil {
			t.Fatal(err)
		}
		lh := s.LeaseHandler()
		mux := http.NewServeMux()
		mux.Handle("/", s.RaftHandler())
		mux.Handle(leasehttp.LeasePrefix, lh)
		mux.Handle(leasehttp.LeaseInternalPrefix, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if block.Load() {
				<-r.Context().Done()
				return
			}
			lh.ServeHTTP(w, r)
		}))
		go http.Serve(l, mux)
		srvs[i] = s
	}
	for _, s := range srvs {
		s.Start()
		defer s.Stop()
	}
	var f *etcdserver.EtcdServer
	for d := time.Now().Add(20 * time.Second); time.Now().Before(d) && f == nil; time.Sleep(50 * time.Millisecond) {
		for _, s := range srvs {
			if s.Leader() != 0 && s.Leader() != s.MemberID() {
				f = s
				break
			}
		}
	}
	if f == nil {
		t.Fatal("no follower with a leader")
	}
	// sanity: a plain context with a context-error cause gets an answer or an error, no panic
	plain, cancelPlain := context.WithTimeout(context.Background(), 5*time.Second)
	if _, err := f.LeaseTimeToLive(plain, &pb.LeaseTimeToLiveRequest{ID: 1}); err != nil {
		t.Logf("plain context: err %v (expected ErrLeaseNotFound)", err)
	}
	cancelPlain()
	block.Store(true)
	ctx, cancel := context.WithDeadlineCause(context.Background(), time.Now().Add(500*time.Millisecond), causeBadErr{})
	defer cancel()
	panicked := func() (r any) {
		defer func() { r = recover() }()
		f.LeaseTimeToLive(ctx, &pb.LeaseTimeToLiveRequest{ID: 1})
		return nil
	}()
	if panicked == nil {
		t.Fatal("follower's LeaseTimeToLive did not panic (the T-k claim no longer holds: update the notes)")
	}
	t.Logf("recovered: %v", panicked)
}
