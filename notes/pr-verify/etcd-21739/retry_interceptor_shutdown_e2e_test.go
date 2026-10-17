package clientv3_test

import (
	"context"
	"net"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// authSrv: the first Authenticate (clientv3.New's) answers a token; later ones
// block until the caller goes away.
type authSrv struct {
	pb.UnimplementedAuthServer
	n       atomic.Int32
	blocked chan struct{}
}

func (a *authSrv) Authenticate(ctx context.Context, _ *pb.AuthenticateRequest) (*pb.AuthenticateResponse, error) {
	if a.n.Add(1) == 1 {
		return &pb.AuthenticateResponse{Token: "tok"}, nil
	}
	select {
	case a.blocked <- struct{}{}:
	default:
	}
	<-ctx.Done()
	return nil, ctx.Err()
}

// watchSrv: every watch stream fails at once with Unavailable, so the client's
// watcher reopens it (openWatchClient -> stream interceptor -> getToken).
type watchSrv struct{ pb.UnimplementedWatchServer }

func (watchSrv) Watch(pb.Watch_WatchServer) error {
	return status.Error(codes.Unavailable, "go away")
}

// TestReviewerE2EShutdownLogs: a real grpc server and a real client with
// auth; a watch whose stream reopen is blocked in Authenticate when Close()
// is called. Prints every warn/error log written.
func TestReviewerE2EShutdownLogs(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := grpc.NewServer()
	as := &authSrv{blocked: make(chan struct{}, 1)}
	pb.RegisterAuthServer(srv, as)
	pb.RegisterWatchServer(srv, watchSrv{})
	go srv.Serve(lis)
	defer srv.Stop()

	core, logs := observer.New(zapcore.DebugLevel)
	cli, err := clientv3.New(clientv3.Config{
		Endpoints:   []string{lis.Addr().String()},
		Username:    "u",
		Password:    "p",
		DialTimeout: 5 * time.Second,
		Logger:      zap.New(core),
	})
	if err != nil {
		t.Fatal(err)
	}
	go cli.Watch(context.Background(), "k")
	select {
	case <-as.blocked:
	case <-time.After(10 * time.Second):
		t.Fatal("no blocked Authenticate")
	}
	cli.Close()
	time.Sleep(500 * time.Millisecond)
	n := 0
	for _, e := range logs.All() {
		if e.Level >= zapcore.WarnLevel {
			n++
			t.Logf("%v %q %v", e.Level, e.Message, e.ContextMap())
		}
	}
	if n != 0 {
		t.Errorf("%d warn/error logs on Close()", n)
	}
}
