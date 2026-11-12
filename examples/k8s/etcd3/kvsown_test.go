package etcd3

import (
	"context"
	"fmt"
	"net"
	"net/http/httptest"
	"os"
	"sync"
	"sync/atomic"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
	"golang.org/x/net/trace"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type kvsOwnKV struct {
	pb.UnimplementedKVServer
	n atomic.Int64
}

func (f *kvsOwnKV) Range(ctx context.Context, r *pb.RangeRequest) (*pb.RangeResponse, error) {
	if f.n.Add(1)%3 != 0 { // two of every three attempts fail: forces the retry interceptor
		return nil, status.Error(codes.Unavailable, "try again")
	}
	resp := &pb.RangeResponse{Header: &pb.ResponseHeader{Revision: 7}, Count: 5}
	for i := 0; i < 5; i++ {
		resp.Kvs = append(resp.Kvs, &mvccpb.KeyValue{Key: []byte(fmt.Sprintf("/k/%d", i)), Value: []byte("v")})
	}
	return resp, nil
}

func kvsOwnStart(t *testing.T) *kubernetes.Client {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	pb.RegisterKVServer(s, &kvsOwnKV{})
	go s.Serve(lis)
	t.Cleanup(s.Stop)
	c, err := kubernetes.New(clientv3.Config{Endpoints: []string{lis.Addr().String()}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { c.Close() })
	return c
}

func kvsOwnHammer(t *testing.T, kc *kubernetes.Client, iters int, render func()) {
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := 0; i < iters; i++ {
				resp, err := kc.List(context.Background(), "/k/", kubernetes.ListOptions{})
				if err != nil {
					t.Error(err)
					return
				}
				if len(resp.Kvs) != 5 {
					t.Errorf("len %d", len(resp.Kvs))
				}
				for j := range resp.Kvs { // as apiserver's appendChunk does
					resp.Kvs[j] = nil
				}
				if render != nil {
					render()
				}
			}
		}()
	}
	wg.Wait()
}

// TestDefaultNoRace (k8s 7e-1, K1, decided by etcd-grove-81): the evidence for the owned reply
// `Kvs` of `grpcInvokerOk`/`RepSat` (`recvOwn`): after `kubernetes.Client.List` returns, the
// caller writes `resp.Kvs[j] = nil` (as apiserver's appendChunk does) while other calls and
// etcd's retries (two of every three attempts fail Unavailable) run; under -race nothing else
// touches the array. The bound `grpc.EnableTracing = false` is needed: with tracing on, grpc keeps
// every reply for /debug/requests (`notes/k8s-7e-1-handoff.md`, TestTracingRace).
func TestDefaultNoRace(t *testing.T) {
	kvsOwnHammer(t, kvsOwnStart(t), 50, nil)
}

// TestTracingRace is TestDefaultNoRace's positive control (the Freeze review of k8s 7e, 2026-11-10):
// the same harness with a component that keeps the reply, grpc's tracing (`grpc.EnableTracing = true`,
// which etcd's SetupGlobalLoggers sets at log level debug: the client trace keeps each reply and
// formats it lazily when /debug/requests is rendered). Under -race it must FAIL with a data race on
// the Kvs array, which shows the harness catches a retained reply. It runs only with
// K8S_KVSOWN_CONTROL=1 (gates 9d runs it so and requires the failure); skipped otherwise.
func TestTracingRace(t *testing.T) {
	if os.Getenv("K8S_KVSOWN_CONTROL") != "1" {
		t.Skip("positive control: run with K8S_KVSOWN_CONTROL=1 under -race; it must fail")
	}
	grpc.EnableTracing = true
	defer func() { grpc.EnableTracing = false }()
	c := kvsOwnStart(t)
	var mu sync.Mutex
	render := func() {
		mu.Lock()
		defer mu.Unlock()
		w := httptest.NewRecorder()
		trace.Render(w, httptest.NewRequest("GET", "/debug/requests?fam=grpc.Sent.etcdserverpb.KV&b=0&exp=1", nil), true)
	}
	// 200 calls per goroutine, not TestDefaultNoRace's 50: one run is more likely to hit the race
	// under load (gates 9d also retries a run that misses it, up to 3 attempts)
	kvsOwnHammer(t, c, 200, render)
}
