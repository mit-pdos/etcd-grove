// Package rtctx checks Addendum T-i of k8s 7f-4 (notes/k8s-7f4-freeze.md;
// notes/roundtripper-ctx-refuted.md): the round trippers rafthttp builds (NewRoundTripper,
// newStreamRoundTripper: a *http.Transport from etcd's transport.NewTimeoutTransport) read the
// request's context, so http.WithContext_ok and the roundTripperOk contract of
// rafthttp.NewRoundTripper.wp_proof / newStreamRoundTripper.wp_proof, which said nothing of it,
// were false; and the fixed contract's premise, a *cancelCtx child of Background()
// (context.bgCancelChild), holds of what rafthttp passes and is enough.
//
//   - Refutation (TestRoundTripValuePanics, TestRoundTripTraceHook, TestRoundTripProgramErr): a
//     context whose Value panics at httptrace's key makes RoundTrip panic; a ClientTrace in the
//     context makes RoundTrip run the program's hooks; on a done context RoundTrip returns the
//     context's own error (here a program error whose Error() panics), not an error net/http made.
//   - Why not isContext with nil values (TestRoundTripDeadlineCause): a context of Perennial's
//     model, WithDeadlineCause(Background(), d, cause), nil at every key, makes RoundTrip return
//     the program's cause (context.Cause), so the premise names WithCancel(Background()).
//   - The fixed premise (TestRoundTripBgCancel): over a WithCancel(Background()) context,
//     RoundTrip of both round trippers returns a response, or an error net/http made (a dial
//     error), or context.Canceled itself once the context is cancelled (in flight or before);
//     over TLS too (TestRoundTripBgCancelTLS: cancelled before the call or during the handshake).
package rtctx

import (
	"context"
	"errors"
	"fmt"
	"net"
	"net/http"
	"net/http/httptest"
	"net/http/httptrace"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
	"go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
)

func pipelineRt(t *testing.T) http.RoundTripper {
	rt, err := rafthttp.NewRoundTripper(transport.TLSInfo{}, time.Second)
	if err != nil {
		t.Fatal(err)
	}
	return rt
}

// panicTraceCtx is a WithCancel(Background()) context but for Value at httptrace's key, which panics.
type panicTraceCtx struct{ context.Context }

func (c panicTraceCtx) Value(k any) any {
	if fmt.Sprintf("%T", k) == "httptrace.clientEventContextKey" {
		panic("Value(httptrace key)")
	}
	return c.Context.Value(k)
}

func expectPanic(t *testing.T, want string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("RoundTrip did not panic (want %q)", want)
		}
		if r != want {
			t.Fatalf("panic %v, want %q", r, want)
		}
		t.Logf("recovered: %v", r)
	}()
	f()
}

func newReq(t *testing.T, url string, ctx context.Context) *http.Request {
	req, err := http.NewRequest("POST", url+"/raft", nil)
	if err != nil {
		t.Fatal(err)
	}
	return req.WithContext(ctx)
}

func TestRoundTripValuePanics(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(http.ResponseWriter, *http.Request) {}))
	defer hs.Close()
	inner, cancel := context.WithCancel(context.Background())
	defer cancel()
	expectPanic(t, "Value(httptrace key)", func() {
		pipelineRt(t).RoundTrip(newReq(t, hs.URL, panicTraceCtx{inner}))
	})
}

func TestRoundTripTraceHook(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(http.ResponseWriter, *http.Request) {}))
	defer hs.Close()
	ctx := httptrace.WithClientTrace(context.Background(),
		&httptrace.ClientTrace{GetConn: func(string) { panic("GetConn hook") }})
	expectPanic(t, "GetConn hook", func() {
		pipelineRt(t).RoundTrip(newReq(t, hs.URL, ctx))
	})
}

type progErr struct{}

func (progErr) Error() string { panic("progErr.Error") }

// doneCtx: Done closed, Err a program error; Value as Background's (nil everywhere).
type doneCtx struct {
	context.Context
	d chan struct{}
}

func (c doneCtx) Done() <-chan struct{} { return c.d }
func (c doneCtx) Err() error            { return progErr{} }

func TestRoundTripProgramErr(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(http.ResponseWriter, *http.Request) { time.Sleep(time.Second) }))
	defer hs.Close()
	d := make(chan struct{})
	close(d)
	resp, err := pipelineRt(t).RoundTrip(newReq(t, hs.URL, doneCtx{context.Background(), d}))
	if resp != nil {
		t.Fatalf("resp %v", resp)
	}
	if _, ok := err.(progErr); !ok {
		t.Fatalf("err %T, want the context's own progErr", err)
	}
}

func TestRoundTripDeadlineCause(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(http.ResponseWriter, *http.Request) { time.Sleep(time.Second) }))
	defer hs.Close()
	ctx, cancel := context.WithDeadlineCause(context.Background(), time.Now().Add(-time.Second), progErr{})
	defer cancel()
	for _, k := range []any{"x", 1, struct{}{}} {
		if ctx.Value(k) != nil {
			t.Fatalf("Value(%v) non-nil", k)
		}
	}
	resp, err := pipelineRt(t).RoundTrip(newReq(t, hs.URL, ctx))
	if resp != nil {
		t.Fatalf("resp %v", resp)
	}
	if _, ok := err.(progErr); !ok {
		t.Fatalf("err %T, want the program's cause", err)
	}
}

// TestRoundTripBgCancel: the fixed premise, a WithCancel(Background()) context, what rafthttp's
// pipeline.post, snapshotSender.post and streamReader.dial pass.
func TestRoundTripBgCancel(t *testing.T) {
	release := make(chan struct{})
	hs := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Query().Get("slow") != "" {
			select {
			case <-release:
			case <-r.Context().Done():
			}
		}
		w.WriteHeader(204)
	}))
	defer hs.Close()
	defer close(release)
	// a closed port: an error net/http made (a dial error)
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	dead := "http://" + l.Addr().String()
	l.Close()
	for name, mk := range map[string]func() (http.RoundTripper, error){
		"NewRoundTripper": func() (http.RoundTripper, error) {
			return rafthttp.NewRoundTripper(transport.TLSInfo{}, time.Second)
		},
		"newStreamRoundTripper": func() (http.RoundTripper, error) {
			// newStreamRoundTripper (unexported) is NewTimeoutTransport(tlsInfo, dialTimeout,
			// ConnReadTimeout, ConnWriteTimeout) (rafthttp/util.go:59; both timeouts 5s)
			return transport.NewTimeoutTransport(transport.TLSInfo{}, time.Second, 5*time.Second, 5*time.Second)
		},
	} {
		rt, err := mk()
		if err != nil {
			t.Fatal(err)
		}
		// live: a response
		ctx, cancel := context.WithCancel(context.Background())
		resp, err := rt.RoundTrip(newReq(t, hs.URL, ctx))
		if err != nil || resp.StatusCode != 204 {
			t.Fatalf("%s: live: %v %v", name, resp, err)
		}
		resp.Body.Close()
		// dial error
		_, err = rt.RoundTrip(newReq(t, dead, ctx))
		var oe *net.OpError
		if err == nil || !errors.As(err, &oe) || errors.Is(err, context.Canceled) {
			t.Fatalf("%s: dial: %T %v", name, err, err)
		}
		_ = err.Error()
		// cancelled in flight
		go func() { time.Sleep(100 * time.Millisecond); cancel() }()
		req, _ := http.NewRequest("POST", hs.URL+"/raft?slow=1", nil)
		_, err = rt.RoundTrip(req.WithContext(ctx))
		if err != context.Canceled {
			t.Fatalf("%s: in flight: %T %v", name, err, err)
		}
		// already cancelled
		_, err = rt.RoundTrip(newReq(t, hs.URL, ctx))
		if err != context.Canceled {
			t.Fatalf("%s: before: %T %v", name, err, err)
		}
		t.Logf("%s: live 204; dial %T; cancelled: %v", name, oe, err)
	}
}

// TestRoundTripBgCancelTLS: the TLS handshake path (HandshakeContext reads the request's context):
// over a WithCancel(Background()) context, a TLS round trip succeeds; cancelled before the call, or
// during a handshake the peer never answers, RoundTrip returns context.Canceled itself. (The
// ProxyFromEnvironment CONNECT path is argued from the code, not tested: Addendum T-i.)
func TestRoundTripBgCancelTLS(t *testing.T) {
	hs := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { w.WriteHeader(204) }))
	defer hs.Close()
	rt, err := rafthttp.NewRoundTripper(transport.TLSInfo{InsecureSkipVerify: true}, time.Second)
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	resp, err := rt.RoundTrip(newReq(t, hs.URL, ctx))
	if err != nil || resp.StatusCode != 204 {
		t.Fatalf("live: %v %v", resp, err)
	}
	resp.Body.Close()
	// a peer that accepts TCP and never answers the handshake; cancel during it
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	stop := make(chan struct{})
	defer close(stop)
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			go func() { <-stop; c.Close() }()
		}
	}()
	rt2, _ := rafthttp.NewRoundTripper(transport.TLSInfo{InsecureSkipVerify: true}, time.Second)
	go func() { time.Sleep(100 * time.Millisecond); cancel() }()
	_, err = rt2.RoundTrip(newReq(t, "https://"+ln.Addr().String(), ctx))
	if err != context.Canceled {
		t.Fatalf("during handshake: %T %v", err, err)
	}
	_, err = rt.RoundTrip(newReq(t, hs.URL, ctx))
	if err != context.Canceled {
		t.Fatalf("before: %T %v", err, err)
	}
}
