// Package grpcstatusro is the Go evidence of the E1 package (k8s 7f-5a-P, notes/k8s-7f5a-draft.md
// §11.2; notes/axiom-review/grpc-status-immutability.md): grpcStatusRO s c, "s is a *Status nobody
// writes, whose code is c", promised by the producers that build a status fresh, and
// {{ grpcStatusRO s c }} s.Code() {{ RET c }}.
//
// A *Status is not immutable in Go: any package can assign a whole struct, *s = *t, copying the
// unexported field (TestWholeStructWriteChangesCode, the negative: the reason grpcStatusRO is a
// producer's guarantee and not a fact of every Loc). What the producers guarantee is that they never
// write a status after building it and hand it out only through GRPCStatus(), so the status changes
// only if the program itself writes through that pointer, which no sorry-free Lean proof can do
// (grpc's Status is an axiomatized type).
//
//   - nowrite_test.go: no code linked into etcd's client, server and cache, nor Kubernetes' etcd3
//     storage, writes a Status, its *spb.Status, or an Error's *Status (a scan of the type-checked
//     sources), with a negative control;
//   - TestStatusErrorProducers: status.Error, status.Errorf, status.New(c, m).Err(): a *status.Error
//     whose GRPCStatus() is one fixed pointer, fresh per call, with Code() = c and Message() = m,
//     unchanged by every read API (FromError, Code, Convert, Proto() mutated, Details, errors.Is,
//     Error, rpctypes.Error, WithDetails), and nil for codes.OK;
//   - TestNilStatusCode: Code() of a nil *Status is OK (the producer states c = OK for s = nil);
//   - TestErrGRPCInitializers: every ErrGRPC* variable of rpctypes' error.go is initialized by
//     status.Error(codes.X, "...") (parsed), its status has that code and message, and the values of
//     errStringToError are those variables; v3rpc's toGRPCErrorMap values are rpctypes' ErrGRPC*
//     variables or two EtcdErrors (no GRPCStatus);
//   - TestInvokerAndStreamErrors (run under -race): the errors grpc's invoker (ClientConn.Invoke)
//     and client stream (RecvMsg, SendMsg, CloseSend) return, over a real server on an in-memory
//     listener, for every code, with details, for the server's shared ErrGRPC* values, for a
//     cancelled or expired context, a stopped server and a closed connection: GRPCStatus() is a
//     fixed pointer whose Code() is the expected code, read concurrently by other goroutines while
//     grpc keeps running and shuts down (the race detector reports any write grpc makes to a status
//     it handed out), and still the expected code at the end; io.EOF has no GRPCStatus.
//
// Run: GOWORK=off go test -race ./premisefix/grpcstatusro/ (from examples/, under a 32G cap).
package grpcstatusro

import (
	"context"
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"
	"google.golang.org/protobuf/types/known/emptypb"
)

type grpcStatuser interface{ GRPCStatus() *status.Status }

// statusOf: the status GRPCStatus() returns, checking it is the same pointer on every call.
func statusOf(t *testing.T, err error) *status.Status {
	t.Helper()
	gs, ok := err.(grpcStatuser)
	if !ok {
		t.Fatalf("%T has no GRPCStatus", err)
	}
	s := gs.GRPCStatus()
	for i := 0; i < 3; i++ {
		if gs.GRPCStatus() != s {
			t.Fatalf("GRPCStatus() of %v returns different pointers", err)
		}
	}
	return s
}

// exerciseReads: every read API of grpc and etcd on err and its status; none may change the code.
func exerciseReads(t *testing.T, err error, s *status.Status) {
	t.Helper()
	_, _ = status.FromError(err)
	_ = status.Code(err)
	_ = status.Convert(err)
	p := s.Proto()
	if p != nil {
		p.Code = 99
		p.Message = "mutated clone"
	}
	_ = s.Details()
	_ = errors.Is(err, err)
	_ = err.Error()
	_ = fmt.Sprintf("%v %s %+v", err, s, s)
	_ = rpctypes.Error(err)
	_ = rpctypes.ErrorDesc(err)
	if s.Code() != codes.OK {
		if _, werr := s.WithDetails(&emptypb.Empty{}); werr != nil {
			t.Fatal(werr)
		}
	}
}

func TestStatusErrorProducers(t *testing.T) {
	seen := map[*status.Status]bool{}
	for c := codes.OK; c <= codes.Unauthenticated; c++ {
		msg := "m" + strconv.Itoa(int(c))
		producers := map[string]func() error{
			"Error":     func() error { return status.Error(c, msg) },
			"Errorf":    func() error { return status.Errorf(c, "m%d", int(c)) },
			"New().Err": func() error { return status.New(c, msg).Err() },
		}
		for name, mk := range producers {
			for i := 0; i < 2; i++ {
				err := mk()
				if c == codes.OK {
					if err != nil {
						t.Fatalf("%s(OK) = %v, want nil", name, err)
					}
					continue
				}
				if got := fmt.Sprintf("%T", err); got != "*status.Error" {
					t.Fatalf("%s(%v): dynamic type %s", name, c, got)
				}
				s := statusOf(t, err)
				if seen[s] {
					t.Fatalf("%s(%v): status pointer not fresh", name, c)
				}
				seen[s] = true
				if fs, ok := status.FromError(err); !ok || fs != s {
					t.Fatalf("FromError(%s(%v)) = %p, %v; want the GRPCStatus pointer %p", name, c, fs, ok, s)
				}
				exerciseReads(t, err, s)
				if s.Code() != c || s.Message() != msg || status.Code(err) != c || statusOf(t, err) != s {
					t.Fatalf("%s(%v): after the reads, code %v message %q", name, c, s.Code(), s.Message())
				}
			}
		}
	}
}

func TestNilStatusCode(t *testing.T) {
	var s *status.Status
	if s.Code() != codes.OK || s.Message() != "" || s.Err() != nil {
		t.Fatalf("nil *Status: code %v message %q err %v", s.Code(), s.Message(), s.Err())
	}
	if status.Code(nil) != codes.OK {
		t.Fatal("status.Code(nil) != OK")
	}
}

// TestWholeStructWriteChangesCode: the negative. A program that writes through the pointer
// GRPCStatus() returns changes what FromError and Code read: no fact of an arbitrary *Status, only
// of one nobody writes.
func TestWholeStructWriteChangesCode(t *testing.T) {
	err := status.Error(codes.Canceled, "x")
	s := statusOf(t, err)
	c1 := status.Code(err)
	*s = *status.New(codes.Internal, "y")
	if c2 := status.Code(err); c1 == c2 {
		t.Fatalf("the write did not change the code (%v): the negative no longer shows the point", c2)
	}
}

func moduleDir(t *testing.T, mod string) string {
	t.Helper()
	cmd := exec.Command("go", "list", "-m", "-f", "{{.Dir}}", mod)
	cmd.Dir, _ = filepath.Abs("../..")
	cmd.Env = append(os.Environ(), "GOWORK=off")
	out, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	return strings.TrimSpace(string(out))
}

// errGRPCVars: rpctypes' ErrGRPC* variables, by name (TestErrGRPCInitializers checks the list is
// the file's). ErrGRPCClusterIdMismatch is an alias of ErrGRPCClusterIDMismatch (the same value).
var errGRPCVars = map[string]error{
	"ErrGRPCEmptyKey": rpctypes.ErrGRPCEmptyKey, "ErrGRPCKeyNotFound": rpctypes.ErrGRPCKeyNotFound,
	"ErrGRPCValueProvided": rpctypes.ErrGRPCValueProvided, "ErrGRPCLeaseProvided": rpctypes.ErrGRPCLeaseProvided,
	"ErrGRPCTooManyOps": rpctypes.ErrGRPCTooManyOps, "ErrGRPCDuplicateKey": rpctypes.ErrGRPCDuplicateKey,
	"ErrGRPCInvalidClientAPIVersion": rpctypes.ErrGRPCInvalidClientAPIVersion,
	"ErrGRPCInvalidSortOption":       rpctypes.ErrGRPCInvalidSortOption,
	"ErrGRPCCompacted":               rpctypes.ErrGRPCCompacted, "ErrGRPCFutureRev": rpctypes.ErrGRPCFutureRev,
	"ErrGRPCNoSpace": rpctypes.ErrGRPCNoSpace, "ErrGRPCLeaseNotFound": rpctypes.ErrGRPCLeaseNotFound,
	"ErrGRPCLeaseExist": rpctypes.ErrGRPCLeaseExist, "ErrGRPCLeaseTTLTooLarge": rpctypes.ErrGRPCLeaseTTLTooLarge,
	"ErrGRPCWatchCanceled": rpctypes.ErrGRPCWatchCanceled, "ErrGRPCMemberExist": rpctypes.ErrGRPCMemberExist,
	"ErrGRPCPeerURLExist":           rpctypes.ErrGRPCPeerURLExist,
	"ErrGRPCMemberNotEnoughStarted": rpctypes.ErrGRPCMemberNotEnoughStarted,
	"ErrGRPCMemberBadURLs":          rpctypes.ErrGRPCMemberBadURLs, "ErrGRPCMemberNotFound": rpctypes.ErrGRPCMemberNotFound,
	"ErrGRPCMemberNotLearner": rpctypes.ErrGRPCMemberNotLearner, "ErrGRPCLearnerNotReady": rpctypes.ErrGRPCLearnerNotReady,
	"ErrGRPCTooManyLearners": rpctypes.ErrGRPCTooManyLearners, "ErrGRPCClusterIDMismatch": rpctypes.ErrGRPCClusterIDMismatch,
	"ErrGRPCClusterIdMismatch": rpctypes.ErrGRPCClusterIdMismatch, //nolint:staticcheck
	"ErrGRPCRequestTooLarge":   rpctypes.ErrGRPCRequestTooLarge, "ErrGRPCRequestTooManyRequests": rpctypes.ErrGRPCRequestTooManyRequests,
	"ErrGRPCRootUserNotExist": rpctypes.ErrGRPCRootUserNotExist, "ErrGRPCRootRoleNotExist": rpctypes.ErrGRPCRootRoleNotExist,
	"ErrGRPCUserAlreadyExist": rpctypes.ErrGRPCUserAlreadyExist, "ErrGRPCUserEmpty": rpctypes.ErrGRPCUserEmpty,
	"ErrGRPCUserNotFound": rpctypes.ErrGRPCUserNotFound, "ErrGRPCRoleAlreadyExist": rpctypes.ErrGRPCRoleAlreadyExist,
	"ErrGRPCRoleNotFound": rpctypes.ErrGRPCRoleNotFound, "ErrGRPCRoleEmpty": rpctypes.ErrGRPCRoleEmpty,
	"ErrGRPCAuthFailed": rpctypes.ErrGRPCAuthFailed, "ErrGRPCPermissionNotGiven": rpctypes.ErrGRPCPermissionNotGiven,
	"ErrGRPCPermissionDenied": rpctypes.ErrGRPCPermissionDenied, "ErrGRPCRoleNotGranted": rpctypes.ErrGRPCRoleNotGranted,
	"ErrGRPCPermissionNotGranted": rpctypes.ErrGRPCPermissionNotGranted, "ErrGRPCAuthNotEnabled": rpctypes.ErrGRPCAuthNotEnabled,
	"ErrGRPCInvalidAuthToken": rpctypes.ErrGRPCInvalidAuthToken, "ErrGRPCInvalidAuthMgmt": rpctypes.ErrGRPCInvalidAuthMgmt,
	"ErrGRPCAuthOldRevision": rpctypes.ErrGRPCAuthOldRevision, "ErrGRPCNoLeader": rpctypes.ErrGRPCNoLeader,
	"ErrGRPCNotLeader": rpctypes.ErrGRPCNotLeader, "ErrGRPCLeaderChanged": rpctypes.ErrGRPCLeaderChanged,
	"ErrGRPCNotCapable": rpctypes.ErrGRPCNotCapable, "ErrGRPCStopped": rpctypes.ErrGRPCStopped,
	"ErrGRPCTimeout": rpctypes.ErrGRPCTimeout, "ErrGRPCTimeoutDueToLeaderFail": rpctypes.ErrGRPCTimeoutDueToLeaderFail,
	"ErrGRPCTimeoutDueToConnectionLost": rpctypes.ErrGRPCTimeoutDueToConnectionLost,
	"ErrGRPCTimeoutWaitAppliedIndex":    rpctypes.ErrGRPCTimeoutWaitAppliedIndex,
	"ErrGRPCUnhealthy":                  rpctypes.ErrGRPCUnhealthy, "ErrGRPCCorrupt": rpctypes.ErrGRPCCorrupt,
	"ErrGRPCNotSupportedForLearner": rpctypes.ErrGRPCNotSupportedForLearner, "ErrGRPCBadLeaderTransferee": rpctypes.ErrGRPCBadLeaderTransferee,
	"ErrGRPCWrongDowngradeVersionFormat":   rpctypes.ErrGRPCWrongDowngradeVersionFormat,
	"ErrGRPCInvalidDowngradeTargetVersion": rpctypes.ErrGRPCInvalidDowngradeTargetVersion,
	"ErrGRPCDowngradeInProcess":            rpctypes.ErrGRPCDowngradeInProcess, "ErrGRPCNoInflightDowngrade": rpctypes.ErrGRPCNoInflightDowngrade,
	"ErrGRPCCanceled": rpctypes.ErrGRPCCanceled, "ErrGRPCClusterVersionUnavailable": rpctypes.ErrGRPCClusterVersionUnavailable, "ErrGRPCDeadlineExceeded": rpctypes.ErrGRPCDeadlineExceeded,
}

func TestErrGRPCInitializers(t *testing.T) {
	file := filepath.Join(moduleDir(t, "go.etcd.io/etcd/api/v3"), "v3rpc", "rpctypes", "error.go")
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, file, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	type init struct{ code, msg string }
	inits := map[string]init{}
	aliases := map[string]string{}
	var mapValues []string
	for _, d := range af.Decls {
		gd, ok := d.(*ast.GenDecl)
		if !ok || gd.Tok != token.VAR {
			continue
		}
		for _, sp := range gd.Specs {
			vs := sp.(*ast.ValueSpec)
			for i, n := range vs.Names {
				if i >= len(vs.Values) {
					continue
				}
				v := vs.Values[i]
				if n.Name == "errStringToError" {
					for _, el := range v.(*ast.CompositeLit).Elts {
						id, ok := el.(*ast.KeyValueExpr).Value.(*ast.Ident)
						if !ok {
							t.Fatalf("errStringToError value %s is not a variable", fset.Position(el.Pos()))
						}
						mapValues = append(mapValues, id.Name)
					}
					continue
				}
				if !strings.HasPrefix(n.Name, "ErrGRPC") {
					continue
				}
				if id, ok := v.(*ast.Ident); ok {
					aliases[n.Name] = id.Name
					continue
				}
				call, ok := v.(*ast.CallExpr)
				sel, ok2 := call.Fun.(*ast.SelectorExpr)
				if !ok || !ok2 || sel.X.(*ast.Ident).Name != "status" || sel.Sel.Name != "Error" || len(call.Args) != 2 {
					t.Fatalf("%s: %s is not initialized by status.Error(c, msg)", fset.Position(n.Pos()), n.Name)
				}
				csel := call.Args[0].(*ast.SelectorExpr)
				lit := call.Args[1].(*ast.BasicLit)
				msg, _ := strconv.Unquote(lit.Value)
				inits[n.Name] = init{csel.Sel.Name, msg}
			}
		}
	}
	if len(inits)+len(aliases) != len(errGRPCVars) {
		t.Fatalf("error.go has %d ErrGRPC* variables (%d aliases), the test lists %d", len(inits)+len(aliases), len(aliases), len(errGRPCVars))
	}
	ptrs := map[*status.Status]string{}
	for name, e := range errGRPCVars {
		in, ok := inits[name]
		if a, isAlias := aliases[name]; isAlias {
			if e != errGRPCVars[a] {
				t.Fatalf("%s is not the value of %s", name, a)
			}
			continue
		}
		if !ok {
			t.Fatalf("%s not in error.go", name)
		}
		s := statusOf(t, e)
		if other, dup := ptrs[s]; dup {
			t.Fatalf("%s and %s share a status", name, other)
		}
		ptrs[s] = name
		exerciseReads(t, e, s)
		if s.Code().String() != in.code || s.Message() != in.msg {
			t.Fatalf("%s: code %v message %q, initializer %s %q", name, s.Code(), s.Message(), in.code, in.msg)
		}
	}
	for _, v := range mapValues {
		if _, ok := inits[v]; !ok {
			t.Fatalf("errStringToError value %s is not an ErrGRPC* initializer", v)
		}
	}
	t.Logf("%d ErrGRPC* initializers, %d aliases, %d errStringToError values", len(inits), len(aliases), len(mapValues))

	// v3rpc's toGRPCErrorMap: its values are rpctypes.ErrGRPC* variables, or rpctypes'
	// ErrMemberNotEnoughStarted / ErrTooManyRequests (EtcdErrors: no GRPCStatus).
	ufile := filepath.Join(moduleDir(t, "go.etcd.io/etcd/server/v3"), "etcdserver", "api", "v3rpc", "util.go")
	uf, err := parser.ParseFile(fset, ufile, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	n := 0
	ast.Inspect(uf, func(nd ast.Node) bool {
		vs, ok := nd.(*ast.ValueSpec)
		if !ok || len(vs.Names) != 1 || vs.Names[0].Name != "toGRPCErrorMap" {
			return true
		}
		for _, el := range vs.Values[0].(*ast.CompositeLit).Elts {
			sel, ok := el.(*ast.KeyValueExpr).Value.(*ast.SelectorExpr)
			if !ok || sel.X.(*ast.Ident).Name != "rpctypes" {
				t.Fatalf("toGRPCErrorMap value at %s is not an rpctypes variable", fset.Position(el.Pos()))
			}
			name := sel.Sel.Name
			if _, ok := inits[name]; !ok && name != "ErrMemberNotEnoughStarted" && name != "ErrTooManyRequests" {
				t.Fatalf("toGRPCErrorMap value rpctypes.%s is not an ErrGRPC* initializer", name)
			}
			n++
		}
		return false
	})
	if n == 0 {
		t.Fatal("toGRPCErrorMap not found")
	}
	for _, e := range []error{rpctypes.ErrMemberNotEnoughStarted, rpctypes.ErrTooManyRequests} {
		if _, ok := e.(grpcStatuser); ok {
			t.Fatalf("%T has GRPCStatus", e)
		}
	}
	t.Logf("toGRPCErrorMap: %d values", n)
}

// The test server: an unknown-service handler whose method name selects the error.
func handler(srv any, ss grpc.ServerStream) error {
	m, _ := grpc.MethodFromServerStream(ss)
	parts := strings.Split(strings.TrimPrefix(m, "/"), "/")
	op := parts[len(parts)-1]
	switch {
	case strings.HasPrefix(op, "code"):
		c, _ := strconv.Atoi(strings.TrimPrefix(op, "code"))
		_ = ss.RecvMsg(&emptypb.Empty{})
		return status.Error(codes.Code(c), "server "+op)
	case op == "details":
		s, _ := status.New(codes.FailedPrecondition, "with details").WithDetails(&emptypb.Empty{})
		return s.Err()
	case strings.HasPrefix(op, "etcd"):
		// The server's shared ErrGRPC* values (as etcd's v3rpc returns them).
		return errGRPCVars[strings.TrimPrefix(op, "etcd")]
	case op == "block":
		<-ss.Context().Done()
		return ss.Context().Err()
	case op == "ok":
		_ = ss.RecvMsg(&emptypb.Empty{})
		return ss.SendMsg(&emptypb.Empty{})
	}
	return status.Error(codes.Unimplemented, op)
}

type collected struct {
	mu   sync.Mutex
	errs []error
	sts  []*status.Status
	want []codes.Code
}

func (c *collected) add(t *testing.T, err error, want codes.Code) {
	t.Helper()
	if err == nil {
		t.Fatalf("nil error, want %v", want)
	}
	s := statusOf(t, err)
	if s.Code() != want {
		t.Fatalf("%v: code %v, want %v", err, s.Code(), want)
	}
	c.mu.Lock()
	c.errs = append(c.errs, err)
	c.sts = append(c.sts, s)
	c.want = append(c.want, want)
	c.mu.Unlock()
}

func (c *collected) snapshot() ([]error, []*status.Status, []codes.Code) {
	c.mu.Lock()
	defer c.mu.Unlock()
	return append([]error(nil), c.errs...), append([]*status.Status(nil), c.sts...), append([]codes.Code(nil), c.want...)
}

func TestInvokerAndStreamErrors(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	srv := grpc.NewServer(grpc.UnknownServiceHandler(handler))
	go func() { _ = srv.Serve(lis) }()
	dial := func() *grpc.ClientConn {
		cc, err := grpc.NewClient("passthrough:///bufnet",
			grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
			grpc.WithTransportCredentials(insecure.NewCredentials()))
		if err != nil {
			t.Fatal(err)
		}
		return cc
	}
	cc := dial()
	var col collected

	// Readers: read every collected status concurrently while grpc runs (the race detector
	// reports a write by grpc to a status it handed out).
	stop := make(chan struct{})
	var readers sync.WaitGroup
	var reads atomic.Int64
	for r := 0; r < 4; r++ {
		readers.Add(1)
		go func() {
			defer readers.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				errs, sts, want := col.snapshot()
				for i, s := range sts {
					if s.Code() != want[i] || status.Code(errs[i]) != want[i] {
						panic(fmt.Sprintf("status %d changed: %v, want %v", i, s.Code(), want[i]))
					}
					_ = s.Message()
					_ = s.Proto()
					_, _ = status.FromError(errs[i])
					reads.Add(1)
				}
				time.Sleep(100 * time.Microsecond)
			}
		}()
	}

	ctx := context.Background()
	in, out := &emptypb.Empty{}, &emptypb.Empty{}
	for round := 0; round < 3; round++ {
		// Unary invoker: every non-OK code from the server.
		for c := codes.Canceled; c <= codes.Unauthenticated; c++ {
			err := cc.Invoke(ctx, fmt.Sprintf("/t.S/code%d", int(c)), in, out)
			col.add(t, err, c)
		}
		col.add(t, cc.Invoke(ctx, "/t.S/details", in, out), codes.FailedPrecondition)
		// The server's shared ErrGRPC* values.
		for _, name := range []string{"ErrGRPCCompacted", "ErrGRPCFutureRev", "ErrGRPCNoLeader", "ErrGRPCNotSupportedForLearner", "ErrGRPCPermissionDenied"} {
			col.add(t, cc.Invoke(ctx, "/t.S/etcd"+name, in, out), statusOf(t, errGRPCVars[name]).Code())
		}
		// Client stream: RecvMsg returns the server's status.
		for _, c := range []codes.Code{codes.Canceled, codes.OutOfRange, codes.Unavailable, codes.Internal} {
			st, err := cc.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, fmt.Sprintf("/t.S/code%d", int(c)))
			if err != nil {
				t.Fatal(err)
			}
			if err := st.SendMsg(in); err != nil && err != io.EOF {
				t.Fatalf("SendMsg: %v", err)
			}
			if err := st.CloseSend(); err != nil {
				t.Fatalf("CloseSend: %v", err)
			}
			col.add(t, st.RecvMsg(out), c)
			// After the status, RecvMsg returns it again; SendMsg returns io.EOF (no GRPCStatus).
			col.add(t, st.RecvMsg(out), c)
			if err := st.SendMsg(in); err != io.EOF {
				if _, ok := err.(grpcStatuser); !ok || err == nil {
					t.Fatalf("SendMsg after the status: %v", err)
				}
				col.add(t, err, statusOf(t, err).Code())
			} else if _, ok := any(err).(grpcStatuser); ok {
				t.Fatal("io.EOF has GRPCStatus")
			}
		}
		// A successful stream: RecvMsg's io.EOF after the message.
		st, err := cc.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, "/t.S/ok")
		if err != nil {
			t.Fatal(err)
		}
		_ = st.SendMsg(in)
		_ = st.CloseSend()
		if err := st.RecvMsg(out); err != nil {
			t.Fatal(err)
		}
		if err := st.RecvMsg(out); err != io.EOF {
			t.Fatalf("RecvMsg after the message: %v, want io.EOF", err)
		}
		// Cancelled and expired contexts: before the call, during a blocked call and stream.
		cctx, cancel := context.WithCancel(ctx)
		cancel()
		col.add(t, cc.Invoke(cctx, "/t.S/ok", in, out), codes.Canceled)
		dctx, dcancel := context.WithTimeout(ctx, time.Millisecond)
		col.add(t, cc.Invoke(dctx, "/t.S/block", in, out), codes.DeadlineExceeded)
		dcancel()
		bctx, bcancel := context.WithCancel(ctx)
		st, err = cc.NewStream(bctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, "/t.S/block")
		if err != nil {
			t.Fatal(err)
		}
		go func() { time.Sleep(time.Millisecond); bcancel() }()
		col.add(t, st.RecvMsg(out), codes.Canceled)
	}

	// A closed connection: Invoke and NewStream return ErrClientConnClosing (a package-level
	// status.Error of grpc's, shared and never written).
	cc2 := dial()
	if err := cc2.Invoke(ctx, "/t.S/ok", in, out); err != nil {
		t.Fatal(err)
	}
	_ = cc2.Close()
	col.add(t, cc2.Invoke(ctx, "/t.S/ok", in, out), codes.Canceled)
	_, err := cc2.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true}, "/t.S/ok")
	col.add(t, err, codes.Canceled)

	// A stopped server, with a stream open: the stream's RecvMsg, then new calls, fail.
	st, err := cc.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, "/t.S/block")
	if err != nil {
		t.Fatal(err)
	}
	time.Sleep(10 * time.Millisecond)
	srv.Stop()
	if err := st.RecvMsg(out); err != nil {
		col.add(t, err, statusOf(t, err).Code())
	}
	sctx, scancel := context.WithTimeout(ctx, 200*time.Millisecond)
	if err := cc.Invoke(sctx, "/t.S/ok", in, out); err != nil {
		col.add(t, err, statusOf(t, err).Code())
	}
	scancel()
	_ = cc.Close()
	time.Sleep(20 * time.Millisecond) // let grpc's goroutines finish while the readers run

	close(stop)
	readers.Wait()
	errs, sts, want := col.snapshot()
	for i, s := range sts {
		if s.Code() != want[i] || statusOf(t, errs[i]) != s {
			t.Fatalf("status %d: code %v, want %v", i, s.Code(), want[i])
		}
	}
	t.Logf("%d errors with a status, %d concurrent reads", len(sts), reads.Load())
	if reads.Load() == 0 {
		t.Fatal("the readers read nothing")
	}
}
