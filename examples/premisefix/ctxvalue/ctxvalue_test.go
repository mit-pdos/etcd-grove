// Package ctxvalue checks the premises of premise fixes 7 (2026-11-11) on contexts' Value and on
// a stream handler's error. Scope: /shared/tmp/premise-fixes-7/scope.md (parts A and B).
//
// Part A: the trust-boundary specs of grpc's metadata (FromOutgoingContext,
// AppendToOutgoingContext), clientv3's WithRequireLeader and streamKeyFromCtx, v3rpc's
// logUnaryRequestStats (and, for premise fixes 8, FromIncomingContext and
// authStore.AuthInfoFromTLS) read ctx.Value at a library's own unexported key (grpc's
// mdOutgoingKey, mdIncomingKey, peerKey; otel's currentSpanKey). The old premises (isContext,
// watchCtx, or none) do not constrain Value there, so a context whose Value panics, or returns a
// value the library code did not build, makes them panic or contradicts their posts
// (TestBadContextPanics, TestContradictions). The new premise (context.libCtxOk and its parts,
// Proof/context/LibKeys.lean) says Value there returns nil, a value of another type, or one the
// library made (metadata.transportMD, metadata.builtRawMD, peer.transportPeer, trace.otelSpan),
// deterministically at the md keys; the standard contexts and grpc's server contexts satisfy it
// (TestRealContexts).
//
// Part B: a stream handler's error reaches status.FromError (grpc's processStreamingRPC, and
// go-grpc-middleware's prometheus reporter), which calls its Error(): a handler returning an
// error whose Error() panics kills the server (TestStreamHandlerErrorPanics). The stream
// contracts now carry srvErrOk on the handler's error (Proof/google_golang_org/grpc/
// InvGrpcStream.lean), and grpc's RecvMsg error other than io.EOF is a status error
// (TestRealStreamErrors).
package ctxvalue

import (
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"errors"
	"fmt"
	"io"
	"math/big"
	"net"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"

	grpcprom "github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/auth"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/peer"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/emptypb"
)

// panicCtx: a Context whose Value panics at every key (Deadline, Done and Err are Background's).
type panicCtx struct{ context.Context }

func (panicCtx) Value(any) any { panic("Value") }

// altCtx: a Context whose Value alternates between two contexts' answers.
type altCtx struct {
	context.Context
	a, b context.Context
	n    *int
}

func (c altCtx) Value(k any) any {
	*c.n++
	if *c.n%2 == 0 {
		return c.a.Value(k)
	}
	return c.b.Value(k)
}

func panics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}

// logUnaryRequestStats's peer read (v3rpc interceptor.go:104-107), replicated: the function is
// unexported.
func remoteOf(ctx context.Context) string {
	remote := "No remote client info."
	peerInfo, ok := peer.FromContext(ctx)
	if ok {
		remote = peerInfo.Addr.String()
	}
	return remote
}

// streamKeyFromCtx (clientv3 watch.go:1102-1107), replicated: the function is unexported.
func streamKeyFromCtx(ctx context.Context) string {
	if md, ok := metadata.FromOutgoingContext(ctx); ok {
		return fmt.Sprintf("%+v", map[string][]string(md))
	}
	return ""
}

func newAuthStore(t *testing.T) auth.AuthStore {
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, be) })
	tp, err := auth.NewTokenProvider(zap.NewNop(), "simple", func(index uint64) <-chan struct{} {
		ch := make(chan struct{})
		close(ch)
		return ch
	}, time.Minute)
	if err != nil {
		t.Fatal(err)
	}
	return auth.NewAuthStore(zap.NewNop(), schema.NewAuthBackend(zap.NewNop(), be), tp, 4)
}

// The old premises admitted these contexts; the functions panic on them.
func TestBadContextPanics(t *testing.T) {
	as := newAuthStore(t)
	bad := map[string]context.Context{
		"nil":      nil,
		"panicCtx": panicCtx{context.Background()},
	}
	for name, ctx := range bad {
		fs := map[string]func(){
			"peer.FromContext":                 func() { peer.FromContext(ctx) },
			"metadata.FromIncomingContext":     func() { metadata.FromIncomingContext(ctx) },
			"metadata.FromOutgoingContext":     func() { metadata.FromOutgoingContext(ctx) },
			"metadata.AppendToOutgoingContext": func() { metadata.AppendToOutgoingContext(ctx, "k", "v") },
			"clientv3.WithRequireLeader":       func() { clientv3.WithRequireLeader(ctx) },
			"streamKeyFromCtx":                 func() { streamKeyFromCtx(ctx) },
			"logUnaryRequestStats' peer read":  func() { remoteOf(ctx) },
			"authStore.AuthInfoFromTLS":        func() { as.AuthInfoFromTLS(ctx) },
		}
		for fname, f := range fs {
			if !panics(f) {
				t.Errorf("%s(%s): expected a panic", fname, name)
			}
		}
	}
	// A typed-nil *Peer, and a *Peer with a nil Addr, under grpc's own key (peer.NewContext is
	// exported): logUnaryRequestStats' Addr.String() panics. transportPeer excludes both.
	for name, p := range map[string]*peer.Peer{"typed nil": nil, "nil Addr": {}} {
		ctx := peer.NewContext(context.Background(), p)
		if !panics(func() { remoteOf(ctx) }) {
			t.Errorf("logUnaryRequestStats' peer read (%s peer): expected a panic", name)
		}
	}
	// A TLSInfo whose verified chain holds a nil certificate: AuthInfoFromTLS reads
	// chains[0].Subject. transportPeer excludes it (crypto/tls never verifies a nil certificate).
	ctx := peer.NewContext(context.Background(), &peer.Peer{
		Addr:     &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 1},
		AuthInfo: credentials.TLSInfo{State: tls.ConnectionState{VerifiedChains: [][]*x509.Certificate{{nil}}}},
	})
	if !panics(func() { as.AuthInfoFromTLS(ctx) }) {
		t.Error("AuthInfoFromTLS (nil certificate in a verified chain): expected a panic")
	}
}

// The old posts claimed what these contexts contradict.
func TestContradictions(t *testing.T) {
	bg := context.Background()
	// FromIncomingContext's old post: every value list is non-empty. NewIncomingContext is
	// exported and stores the program's map as is.
	md, ok := metadata.FromIncomingContext(metadata.NewIncomingContext(bg, metadata.MD{"token": {}}))
	if !ok || len(md["token"]) != 0 {
		t.Fatalf("expected an empty value list, got %v %v", md, ok)
	}
	// outgoingOf/streamKeyOf: functions of the context. A Value alternating between two real
	// contexts' rawMDs makes two calls disagree.
	n := 0
	alt := altCtx{bg, metadata.NewOutgoingContext(bg, metadata.Pairs("a", "1")),
		metadata.NewOutgoingContext(bg, metadata.Pairs("b", "2")), &n}
	k1, k2 := streamKeyFromCtx(alt), streamKeyFromCtx(alt)
	if k1 == k2 {
		t.Fatalf("expected two different stream keys, got %q twice", k1)
	}
	m1, _ := metadata.FromOutgoingContext(alt)
	m2, _ := metadata.FromOutgoingContext(alt)
	if fmt.Sprint(map[string][]string(m1)) == fmt.Sprint(map[string][]string(m2)) {
		t.Fatalf("expected two different outgoing MDs, got %v twice", m1)
	}
	// A raw MD with two keys equal up to case (NewOutgoingContext stores the map as is): which
	// value survives depends on the map's iteration order. builtRawMD excludes it.
	ctx := metadata.NewOutgoingContext(bg, metadata.MD{"A": {"1"}, "a": {"2"}})
	seen := map[string]bool{}
	for i := 0; i < 1000 && len(seen) < 2; i++ {
		seen[streamKeyFromCtx(ctx)] = true
	}
	if len(seen) < 2 {
		t.Log("two keys equal up to case: one stream key in 1000 calls (map order not observed to vary)")
	}
}

// checkNoLibValues: Value at grpc's and otel's keys gives nothing on ctx.
func checkNoLibValues(t *testing.T, name string, ctx context.Context) {
	t.Helper()
	if _, ok := peer.FromContext(ctx); ok {
		t.Errorf("%s: a peer", name)
	}
	if _, ok := metadata.FromIncomingContext(ctx); ok {
		t.Errorf("%s: incoming metadata", name)
	}
	if _, ok := metadata.FromOutgoingContext(ctx); ok {
		t.Errorf("%s: outgoing metadata", name)
	}
	if trace.SpanContextFromContext(ctx).IsValid() {
		t.Errorf("%s: a span", name)
	}
	remoteOf(ctx)
	streamKeyFromCtx(ctx)
}

type otherKey struct{}

func TestRealContexts(t *testing.T) {
	bg := context.Background()
	c1, cancel1 := context.WithCancel(bg)
	defer cancel1()
	c2, cancel2 := context.WithTimeout(context.TODO(), time.Minute)
	defer cancel2()
	c3, cancel3 := context.WithDeadline(context.WithValue(c1, otherKey{}, 1), time.Now().Add(time.Minute))
	defer cancel3()
	for name, ctx := range map[string]context.Context{
		"Background": bg, "TODO": context.TODO(), "WithCancel": c1, "WithTimeout(TODO)": c2,
		"WithDeadline(WithValue(WithCancel))": c3,
	} {
		checkNoLibValues(t, name, ctx)
	}
	// AppendToOutgoingContext and WithRequireLeader: outgoing metadata with lower-case keys, each
	// with a value, the same on every call.
	o1 := metadata.AppendToOutgoingContext(clientv3.WithRequireLeader(bg), "Token", "x")
	o2 := clientv3.WithRequireLeader(metadata.AppendToOutgoingContext(bg, "token", "x"))
	for name, ctx := range map[string]context.Context{"Append(WithRequireLeader)": o1, "WithRequireLeader(Append)": o2} {
		md, ok := metadata.FromOutgoingContext(ctx)
		if !ok || len(md[rpctypes.MetadataRequireLeaderKey]) == 0 || len(md["token"]) == 0 {
			t.Errorf("%s: outgoing metadata %v %v", name, md, ok)
		}
		for k := range md {
			if k != strings.ToLower(k) {
				t.Errorf("%s: key %q", name, k)
			}
		}
		if streamKeyFromCtx(ctx) != streamKeyFromCtx(ctx) {
			t.Errorf("%s: two stream keys", name)
		}
	}
	// grpc's server contexts, insecure and TLS, in a unary and a stream handler, with otelgrpc's
	// server handler and the SDK's tracer.
	for _, useTLS := range []bool{false, true} {
		got := make(chan string, 2)
		check := func(ctx context.Context, kind string) {
			var errs []string
			md, ok := metadata.FromIncomingContext(ctx)
			if !ok || len(md["token"]) == 0 {
				errs = append(errs, fmt.Sprintf("incoming metadata %v %v", md, ok))
			}
			for k, v := range md {
				if k != strings.ToLower(k) || len(v) == 0 {
					errs = append(errs, fmt.Sprintf("incoming key %q %v", k, v))
				}
			}
			p, ok := peer.FromContext(ctx)
			if !ok || p == nil || p.Addr == nil {
				errs = append(errs, fmt.Sprintf("peer %v %v", p, ok))
			} else {
				_ = p.Addr.String()
				switch ai := p.AuthInfo.(type) {
				case nil:
					if useTLS {
						errs = append(errs, "no AuthInfo with TLS")
					}
				case credentials.TLSInfo:
					if len(ai.State.VerifiedChains) == 0 {
						errs = append(errs, "no verified chain")
					}
					for _, ch := range ai.State.VerifiedChains {
						for _, c := range ch {
							if c == nil {
								errs = append(errs, "nil certificate")
							}
						}
					}
				default:
					errs = append(errs, fmt.Sprintf("AuthInfo %T", ai))
				}
			}
			if _, ok := metadata.FromOutgoingContext(ctx); ok {
				errs = append(errs, "outgoing metadata")
			}
			sp := trace.SpanFromContext(ctx)
			if !sp.SpanContext().IsValid() {
				errs = append(errs, "no span")
			}
			_ = sp.TracerProvider().Tracer("t")
			got <- fmt.Sprintf("%s tls=%v: %s", kind, useTLS, strings.Join(errs, "; "))
		}
		unary := func(srv any, ctx context.Context, dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
			in := new(emptypb.Empty)
			if err := dec(in); err != nil {
				return nil, err
			}
			check(ctx, "unary")
			return in, nil
		}
		stream := func(srv any, ss grpc.ServerStream) error {
			check(ss.Context(), "stream")
			return nil
		}
		cc := startServer(t, useTLS, []grpc.ServerOption{
			grpc.StatsHandler(otelgrpc.NewServerHandler(otelgrpc.WithTracerProvider(sdktrace.NewTracerProvider()))),
		}, unary, stream)
		ctx := metadata.AppendToOutgoingContext(bg, "Token", "x")
		if err := cc.Invoke(ctx, "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)); err != nil {
			t.Fatal(err)
		}
		cs, err := cc.NewStream(ctx, &streamDesc, "/t.S/S")
		if err != nil {
			t.Fatal(err)
		}
		if err := cs.RecvMsg(new(emptypb.Empty)); err != io.EOF {
			t.Fatalf("stream: %v", err)
		}
		for i := 0; i < 2; i++ {
			s := <-got
			if !strings.HasSuffix(s, ": ") {
				t.Error(s)
			}
		}
	}
}

var streamDesc = grpc.StreamDesc{StreamName: "S", ServerStreams: true, ClientStreams: true}

// startServer serves t.S/U (unary) and t.S/S (bidirectional stream) on localhost and returns a
// client connection.
func startServer(t *testing.T, useTLS bool, opts []grpc.ServerOption,
	unary func(any, context.Context, func(any) error, grpc.UnaryServerInterceptor) (any, error),
	stream grpc.StreamHandler) *grpc.ClientConn {
	t.Helper()
	cliCreds := insecure.NewCredentials()
	if useTLS {
		srvCfg, cliCfg := tlsConfigs(t)
		opts = append(opts, grpc.Creds(credentials.NewTLS(srvCfg)))
		cliCreds = credentials.NewTLS(cliCfg)
	}
	s := grpc.NewServer(opts...)
	s.RegisterService(&grpc.ServiceDesc{
		ServiceName: "t.S",
		HandlerType: (*any)(nil),
		Methods:     []grpc.MethodDesc{{MethodName: "U", Handler: unary}},
		Streams:     []grpc.StreamDesc{{StreamName: "S", Handler: stream, ServerStreams: true, ClientStreams: true}},
	}, struct{}{})
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	go s.Serve(l)
	t.Cleanup(s.Stop)
	cc, err := grpc.NewClient(l.Addr().String(), grpc.WithTransportCredentials(cliCreds))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cc.Close() })
	return cc
}

// tlsConfigs: a CA, a server certificate for 127.0.0.1 and a client certificate, both signed by
// it; the server requires and verifies the client's.
func tlsConfigs(t *testing.T) (*tls.Config, *tls.Config) {
	t.Helper()
	caKey, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	caTmpl := &x509.Certificate{SerialNumber: big.NewInt(1), Subject: pkix.Name{CommonName: "ca"},
		NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(time.Hour), IsCA: true,
		BasicConstraintsValid: true, KeyUsage: x509.KeyUsageCertSign}
	caDER, err := x509.CreateCertificate(rand.Reader, caTmpl, caTmpl, &caKey.PublicKey, caKey)
	if err != nil {
		t.Fatal(err)
	}
	ca, _ := x509.ParseCertificate(caDER)
	pool := x509.NewCertPool()
	pool.AddCert(ca)
	leaf := func(serial int64, cn string, usage x509.ExtKeyUsage) tls.Certificate {
		key, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
		tmpl := &x509.Certificate{SerialNumber: big.NewInt(serial), Subject: pkix.Name{CommonName: cn},
			NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(time.Hour),
			KeyUsage: x509.KeyUsageDigitalSignature, ExtKeyUsage: []x509.ExtKeyUsage{usage},
			IPAddresses: []net.IP{net.IPv4(127, 0, 0, 1)}}
		der, err := x509.CreateCertificate(rand.Reader, tmpl, ca, &key.PublicKey, caKey)
		if err != nil {
			t.Fatal(err)
		}
		return tls.Certificate{Certificate: [][]byte{der}, PrivateKey: key}
	}
	srv := &tls.Config{Certificates: []tls.Certificate{leaf(2, "server", x509.ExtKeyUsageServerAuth)},
		ClientCAs: pool, ClientAuth: tls.RequireAndVerifyClientCert}
	cli := &tls.Config{Certificates: []tls.Certificate{leaf(3, "root", x509.ExtKeyUsageClientAuth)},
		RootCAs: pool}
	return srv, cli
}

// badErr: an error whose Error() panics.
type badErr struct{}

func (badErr) Error() string { panic("badErr.Error() called") }

// The child of TestStreamHandlerErrorPanics: serves a stream handler returning badErr{} (under
// the prometheus interceptor if PF7_CHILD=prom) and calls it; the server's goroutine panics.
func TestStreamHandlerErrorChild(t *testing.T) {
	mode := os.Getenv("PF7_CHILD")
	if mode == "" {
		t.Skip("run by TestStreamHandlerErrorPanics")
	}
	var opts []grpc.ServerOption
	if mode == "prom" {
		opts = append(opts, grpc.StreamInterceptor(grpcprom.NewServerMetrics().StreamServerInterceptor()))
	}
	cc := startServer(t, false, opts, nil, func(any, grpc.ServerStream) error { return badErr{} })
	cs, err := cc.NewStream(context.Background(), &streamDesc, "/t.S/S")
	if err != nil {
		t.Fatal(err)
	}
	cs.RecvMsg(new(emptypb.Empty))
	time.Sleep(5 * time.Second)
	fmt.Println("child: no panic")
}

func TestStreamHandlerErrorPanics(t *testing.T) {
	for _, mode := range []string{"prom", "plain"} {
		cmd := exec.Command(os.Args[0], "-test.run=^TestStreamHandlerErrorChild$", "-test.count=1")
		cmd.Env = append(os.Environ(), "PF7_CHILD="+mode)
		out, err := cmd.CombinedOutput()
		if err == nil || !strings.Contains(string(out), "badErr.Error() called") {
			t.Errorf("%s: expected the child to die of badErr.Error()'s panic; err %v, output:\n%s", mode, err, out)
		}
	}
}

// grpc's RecvMsg errors, and the errors etcd's Watch and stream interceptor return, are status
// errors (status.FromError's ok), directly and through the prometheus interceptor.
func TestRealStreamErrors(t *testing.T) {
	for _, err := range []error{rpctypes.ErrGRPCWatchCanceled, rpctypes.ErrGRPCNoLeader,
		rpctypes.ErrGRPCNotCapable, context.DeadlineExceeded, context.Canceled} {
		if _, ok := status.FromError(err); !ok && !errors.Is(err, context.Canceled) && !errors.Is(err, context.DeadlineExceeded) {
			t.Errorf("%v: not a status error", err)
		}
		_ = status.Convert(err)
		_ = status.FromContextError(err)
	}
	for _, prom := range []bool{false, true} {
		recvErr := make(chan error, 1)
		var opts []grpc.ServerOption
		if prom {
			opts = append(opts, grpc.StreamInterceptor(grpcprom.NewServerMetrics().StreamServerInterceptor()))
		}
		cc := startServer(t, false, opts, nil, func(_ any, ss grpc.ServerStream) error {
			var err error
			for err == nil {
				err = ss.RecvMsg(new(emptypb.Empty))
			}
			recvErr <- err
			return err
		})
		ctx, cancel := context.WithCancel(context.Background())
		cs, err := cc.NewStream(ctx, &streamDesc, "/t.S/S")
		if err != nil {
			t.Fatal(err)
		}
		if err := cs.SendMsg(new(emptypb.Empty)); err != nil {
			t.Fatal(err)
		}
		cancel()
		err = <-recvErr
		if err == io.EOF {
			t.Fatalf("prom=%v: io.EOF after cancel", prom)
		}
		if _, ok := status.FromError(err); !ok {
			t.Errorf("prom=%v: RecvMsg error %v (%T) not a status error", prom, err, err)
		}
	}
}
