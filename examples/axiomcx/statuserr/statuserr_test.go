package statuserr

// The combined statusErrOk change (stTypedErr + grpcStatusIs), checked on the real code at the pins:
// every error grpc or etcd hands out whose method set has GRPCStatus() *Status is a
// *internal/status.Error; its field s, the Status's field s, and that spb.Status's Code and Message
// are never written after construction, including by grpc's server writing the status (with details:
// RawStatusProto + proto.Marshal) and by the client reading it; the client's error is a fresh
// *status.Error, not the server's object.

import (
	"context"
	"errors"
	"io"
	"net"
	"reflect"
	"testing"
	"time"
	"unsafe"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/health/grpc_health_v1"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"
	"google.golang.org/protobuf/types/known/durationpb"
)

type grpcstatus interface{ GRPCStatus() *status.Status }

// snap is what grpcStatusIs claims fixed: Error.s, Status.s, and the proto's Code and Message.
type snap struct {
	errS, stS uintptr
	code      int32
	msg       string
}

func take(t *testing.T, name string, e error) (snap, bool) {
	t.Helper()
	gs, ok := e.(grpcstatus)
	if !ok {
		return snap{}, false
	}
	ty := reflect.TypeOf(e)
	if ty.Kind() != reflect.Pointer || ty.Elem().PkgPath() != "google.golang.org/grpc/internal/status" ||
		ty.Elem().Name() != "Error" {
		t.Fatalf("%s: has GRPCStatus but is %v", name, ty)
	}
	ev := reflect.ValueOf(e).Elem().Field(0) // Error.s
	st := (*status.Status)(unsafe.Pointer(ev.Pointer()))
	if gs.GRPCStatus() != st {
		t.Fatalf("%s: GRPCStatus() is not Error.s", name)
	}
	sv := reflect.ValueOf(st).Elem().Field(0) // Status.s, a *spb.Status
	if sv.IsNil() {
		t.Fatalf("%s: nil proto", name)
	}
	p := sv.Elem()
	return snap{ev.Pointer(), sv.Pointer(), int32(p.FieldByName("Code").Int()), p.FieldByName("Message").String()}, true
}

func stTyped(t *testing.T, name string, e error) {
	t.Helper()
	v := reflect.ValueOf(e)
	ty := v.Type()
	switch {
	case ty == reflect.TypeOf(rpctypes.EtcdError{}):
		_ = e.(rpctypes.EtcdError)
	case ty.String() == "context.deadlineExceededError":
		if !v.IsZero() || ty.Size() != 0 {
			t.Fatalf("%s: deadlineExceededError not its zero value", name)
		}
	case ty.Kind() == reflect.Pointer:
		_ = v.Pointer()
	}
}

type srv struct {
	grpc_health_v1.UnimplementedHealthServer
	errs map[string]error
}

func (s *srv) Check(ctx context.Context, r *grpc_health_v1.HealthCheckRequest) (*grpc_health_v1.HealthCheckResponse, error) {
	return nil, s.errs[r.Service]
}

func TestStatusErrCombined(t *testing.T) {
	withDet, err := status.New(codes.FailedPrecondition, "det").WithDetails(durationpb.New(time.Second))
	if err != nil {
		t.Fatal(err)
	}
	handlerErrs := map[string]error{
		"noleader":  rpctypes.ErrGRPCNoLeader,
		"fresh":     status.Error(codes.Unavailable, "fresh"),
		"details":   withDet.Err(),
		"etcderr":   rpctypes.ErrTooManyRequests,
		"plain":     errors.New("plain"),
		"ctxcancel": context.Canceled,
	}
	before := map[string]snap{}
	for k, e := range handlerErrs {
		stTyped(t, k, e)
		if s, ok := take(t, k, e); ok {
			before[k] = s
		}
	}
	globals := map[string]error{
		"grpc.ErrClientConnClosing": grpc.ErrClientConnClosing,
		"ErrGRPCNoLeader":           rpctypes.ErrGRPCNoLeader,
		"ErrGRPCCompacted":          rpctypes.ErrGRPCCompacted,
	}
	gbefore := map[string]snap{}
	for k, e := range globals {
		s, _ := take(t, k, e)
		gbefore[k] = s
	}

	lis := bufconn.Listen(1 << 20)
	gs := grpc.NewServer()
	grpc_health_v1.RegisterHealthServer(gs, &srv{errs: handlerErrs})
	go gs.Serve(lis)
	defer gs.Stop()
	cc, err := grpc.NewClient("passthrough:///buf", grpc.WithContextDialer(
		func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	hc := grpc_health_v1.NewHealthClient(cc)
	for round := 0; round < 3; round++ {
		for k := range handlerErrs {
			_, cerr := hc.Check(context.Background(), &grpc_health_v1.HealthCheckRequest{Service: k})
			stTyped(t, "client:"+k, cerr)
			cs, ok := take(t, "client:"+k, cerr)
			if !ok {
				t.Fatalf("client:%s: no GRPCStatus (%T)", k, cerr)
			}
			if b, ok := before[k]; ok && (cs.errS == b.errS || cs.stS == b.stS) {
				t.Fatalf("client:%s: shares the server's object", k)
			}
			if round == 0 {
				t.Logf("client:%-10s %T code=%d msg=%q", k, cerr, cs.code, cs.msg)
			}
		}
	}
	// grpc-made errors on the client: canceled, deadline, closed connection.
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	_, e1 := hc.Check(ctx, &grpc_health_v1.HealthCheckRequest{Service: "fresh"})
	ctx2, cancel2 := context.WithTimeout(context.Background(), time.Nanosecond)
	defer cancel2()
	time.Sleep(time.Millisecond)
	_, e2 := hc.Check(ctx2, &grpc_health_v1.HealthCheckRequest{Service: "fresh"})
	cc.Close()
	_, e3 := hc.Check(context.Background(), &grpc_health_v1.HealthCheckRequest{Service: "fresh"})
	for k, e := range map[string]error{"canceled": e1, "deadline": e2, "closed": e3} {
		stTyped(t, k, e)
		s, ok := take(t, k, e)
		if !ok {
			t.Fatalf("%s: no GRPCStatus (%T)", k, e)
		}
		t.Logf("%-17s %T code=%d msg=%q", k, e, s.code, s.msg)
	}
	if _, ok := take(t, "closed", e3); ok {
		s3, _ := take(t, "closed", e3)
		if s3.errS == gbefore["grpc.ErrClientConnClosing"].errS {
			t.Logf("closed: is grpc.ErrClientConnClosing's object (shared)")
		}
	}
	// nothing written after construction
	for k, b := range before {
		a, _ := take(t, k, handlerErrs[k])
		if a != b {
			t.Fatalf("%s: changed: %+v -> %+v", k, b, a)
		}
	}
	for k, b := range gbefore {
		a, _ := take(t, k, globals[k])
		if a != b {
			t.Fatalf("%s: changed: %+v -> %+v", k, b, a)
		}
	}
	// FromError of a wrapped status: a fresh status, the original unchanged.
	w := errorsJoinW(rpctypes.ErrGRPCNoLeader)
	st, ok := status.FromError(w)
	if !ok || st == rpctypes.ErrGRPCNoLeader.(grpcstatus).GRPCStatus() {
		t.Fatalf("wrapped FromError")
	}
	if a, _ := take(t, "ErrGRPCNoLeader", rpctypes.ErrGRPCNoLeader); a != gbefore["ErrGRPCNoLeader"] {
		t.Fatalf("ErrGRPCNoLeader changed by FromError of a wrapper")
	}
	_ = io.EOF
}

type wrapErr struct{ e error }

func (w wrapErr) Error() string { return "w: " + w.e.Error() }
func (w wrapErr) Unwrap() error { return w.e }

func errorsJoinW(e error) error { return wrapErr{e} }
