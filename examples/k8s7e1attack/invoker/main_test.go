// The attack programs behind k8s 7e-1's restated trust statements (axiom-skill attacks, 2026-11-10;
// notes/k8s-7e-freeze.md): grpc-go v1.84's bare invoker, called the way etcd's unary interceptor gets
// it, returns attempt errors whose dynamic type is *status.Error (a server status, a canceled or
// expired context, a closed connection), the attempt-level claim of grpcInvokerOk's clientErrTys.
package invoker

import (
	"context"
	"errors"
	"fmt"
	"net"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	hpb "google.golang.org/grpc/health/grpc_health_v1"
	"google.golang.org/grpc/status"
)

type srv struct {
	hpb.UnimplementedHealthServer
}

func (srv) Check(ctx context.Context, r *hpb.HealthCheckRequest) (*hpb.HealthCheckResponse, error) {
	switch r.Service {
	case "sleep":
		time.Sleep(300 * time.Millisecond)
	case "err":
		return nil, status.Error(codes.FailedPrecondition, "etcdserver: some error")
	case "unavail":
		return nil, status.Error(codes.Unavailable, "unavail")
	}
	return &hpb.HealthCheckResponse{}, nil
}

type myStErr struct{}

func (myStErr) Error() string              { return "mine" }
func (myStErr) GRPCStatus() *status.Status { return status.New(codes.Unauthenticated, "mine") }

type creds struct{ err error }

func (c creds) GetRequestMetadata(context.Context, ...string) (map[string]string, error) {
	return nil, c.err
}
func (creds) RequireTransportSecurity() bool { return false }

func startServer(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	hpb.RegisterHealthServer(s, srv{})
	go s.Serve(l)
	t.Cleanup(s.Stop)
	return l.Addr().String()
}

// invokeOnly: call the bare invoker the way etcd's interceptor gets it.
func call(t *testing.T, name, addr, svc string, ctx context.Context, close bool, extra ...grpc.DialOption) error {
	var got error
	cap := func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn, inv grpc.UnaryInvoker, opts ...grpc.CallOption) error {
		got = inv(ctx, method, req, reply, cc, opts...)
		return got
	}
	opts := append([]grpc.DialOption{grpc.WithTransportCredentials(insecure.NewCredentials()), grpc.WithUnaryInterceptor(cap)}, extra...)
	cc, err := grpc.NewClient("passthrough:///"+addr, opts...)
	if err != nil {
		t.Fatal(err)
	}
	if close {
		cc.Close()
	} else {
		defer cc.Close()
	}
	_ = cc.Invoke(ctx, "/grpc.health.v1.Health/Check", &hpb.HealthCheckRequest{Service: svc}, &hpb.HealthCheckResponse{})
	var s interface{ GRPCStatus() *status.Status }
	fmt.Printf("%-28s %%T=%-32T as-status=%v err=%v\n", name, got, errors.As(got, &s), got)
	return got
}

// inDefault: an attempt error under etcd's configuration (no per-RPC credentials error, no retry
// policy) is nil or a *status.Error.
func inDefault(t *testing.T, name string, err error) {
	if err == nil {
		return
	}
	if fmt.Sprintf("%T", err) != "*status.Error" { // grpc's internal/status.Error
		t.Errorf("%s: attempt error of type %T, not *status.Error", name, err)
	}
}

func TestTypes(t *testing.T) {
	addr := startServer(t)
	bg := context.Background()
	cctx, cancel := context.WithCancel(bg)
	cancel()
	inDefault(t, "ok", call(t, "ok", addr, "", bg, false))
	inDefault(t, "canceled-before", call(t, "canceled-before", addr, "", cctx, false))
	dctx, c2 := context.WithTimeout(bg, 50*time.Millisecond)
	defer c2()
	inDefault(t, "deadline-in-flight", call(t, "deadline-in-flight", addr, "sleep", dctx, false))
	dctx2, c3 := context.WithTimeout(bg, time.Nanosecond)
	defer c3()
	time.Sleep(time.Millisecond)
	inDefault(t, "deadline-before", call(t, "deadline-before", addr, "", dctx2, false))
	inDefault(t, "server-status", call(t, "server-status", addr, "err", bg, false))
	inDefault(t, "conn-closed", call(t, "conn-closed", addr, "", bg, true))
	inDefault(t, "conn-refused", call(t, "conn-refused", "127.0.0.1:1", "", bg, false))
	call(t, "creds-plain-err", addr, "", bg, false, grpc.WithPerRPCCredentials(creds{errors.New("x")}))
	call(t, "creds-GRPCStatus-type", addr, "", bg, false, grpc.WithPerRPCCredentials(creds{myStErr{}}))
	call(t, "creds-wrapped-status", addr, "", bg, false, grpc.WithPerRPCCredentials(creds{fmt.Errorf("w: %w", status.Error(codes.Unauthenticated, "u"))}))
	sc := `{"methodConfig":[{"name":[{"service":"grpc.health.v1.Health"}],"retryPolicy":{"maxAttempts":2,"initialBackoff":"0.01s","maxBackoff":"0.01s","backoffMultiplier":1,"retryableStatusCodes":["UNAVAILABLE"]}}]}`
	call(t, "retry-policy-exhausted", addr, "unavail", bg, false, grpc.WithDefaultServiceConfig(sc))
}
