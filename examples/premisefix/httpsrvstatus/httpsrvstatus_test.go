// Package httpsrvstatus checks the http-boundary fix of 2026-11-14 (finding 2 of the network fault
// review): RoundTrip can return a status no handler set, one Go's server answers with itself
// (http.srvStatuses, Proof/net/http/Boundary.lean), so roundTripperOk's promise of the protocol's
// resp of the returned status needs every registered protocol to admit those answers
// (http.Proto.srvOk, which http.reserve now asks).
//
//   - The old statement's refutation (TestRoundTrip431, TestRoundTrip417): through rafthttp's round
//     tripper (transport.NewTimeoutTransport), headers over MaxHeaderBytes get 431 and an Expect
//     other than 100-continue gets 417, with no handler run.
//   - The list (TestServerOwnStatuses): over a raw connection, the answers of conn.serve and
//     readRequest (go1.27.3 net/http/server.go:1063, 2083-2123) are 400, 501 and 505, with no
//     handler run; with 431 and 417 they are srvStatuses. Their headers are only Content-Type and
//     Connection (srvKeys), so the client sees empty handler headers (srvOk's rhdr R []).
package httpsrvstatus

import (
	"bufio"
	"net"
	"net/http"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

var srvStatuses = map[int]bool{400: true, 417: true, 431: true, 501: true, 505: true}

func serve(t *testing.T) (string, *atomic.Int32) {
	t.Helper()
	var ran atomic.Int32
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ran.Add(1)
		w.WriteHeader(204)
	})
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	go http.Serve(l, h)
	return l.Addr().String(), &ran
}

func roundTrip(t *testing.T, req *http.Request) *http.Response {
	t.Helper()
	rt, err := transport.NewTimeoutTransport(transport.TLSInfo{}, time.Second, 0, 0)
	if err != nil {
		t.Fatal(err)
	}
	resp, err := rt.RoundTrip(req)
	if err != nil {
		t.Fatalf("RoundTrip: %v", err)
	}
	resp.Body.Close()
	return resp
}

func checkHdrs(t *testing.T, h http.Header) {
	t.Helper()
	for k := range h {
		switch k {
		case "Date", "Content-Type", "Content-Length", "Transfer-Encoding", "Connection",
			"X-Content-Type-Options":
		default:
			t.Errorf("server-made answer sets header %q, not in srvKeys", k)
		}
	}
}

func TestRoundTrip431(t *testing.T) {
	a, ran := serve(t)
	req, _ := http.NewRequest(http.MethodPost, "http://"+a+"/raft", strings.NewReader("x"))
	req.Header.Set("X-PeerURLs", strings.Repeat("a", 2<<20))
	resp := roundTrip(t, req)
	if resp.StatusCode != 431 || ran.Load() != 0 {
		t.Errorf("status %d, handler ran %d times; want 431 and none", resp.StatusCode, ran.Load())
	}
	checkHdrs(t, resp.Header)
}

func TestRoundTrip417(t *testing.T) {
	a, ran := serve(t)
	req, _ := http.NewRequest(http.MethodGet, "http://"+a+"/raft/stream/message/1", nil)
	req.Header.Set("Expect", "something")
	resp := roundTrip(t, req)
	if resp.StatusCode != 417 || ran.Load() != 0 {
		t.Errorf("status %d, handler ran %d times; want 417 and none", resp.StatusCode, ran.Load())
	}
	checkHdrs(t, resp.Header)
}

func TestServerOwnStatuses(t *testing.T) {
	for _, c := range []struct {
		raw  string
		want int
	}{
		{"GET /raft HTTP/1.1\r\n\r\n", 400},                                                     // missing Host
		{"GET /raft HTTP/1.1\r\nHost: a\r\nBad Header: x\r\n\r\n", 400},                         // invalid header name
		{"POST /raft HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip\r\n\r\n", 501},              // unsupported coding
		{"GET /raft HTTP/2.5\r\nHost: a\r\n\r\n", 505},                                          // unsupported version
		{"GET /raft HTTP/1.1\r\nHost: a\r\nExpect: something\r\n\r\n", 417},                     // unknown expectation
		{"GET /raft HTTP/1.1\r\nHost: a\r\nX: " + strings.Repeat("a", 2<<20) + "\r\n\r\n", 431}, // too large
	} {
		a, ran := serve(t)
		conn, err := net.Dial("tcp", a)
		if err != nil {
			t.Fatal(err)
		}
		go conn.Write([]byte(c.raw))
		resp, err := http.ReadResponse(bufio.NewReader(conn), nil)
		if err != nil {
			t.Fatalf("%q: %v", c.raw[:20], err)
		}
		resp.Body.Close()
		conn.Close()
		if resp.StatusCode != c.want || !srvStatuses[resp.StatusCode] || ran.Load() != 0 {
			t.Errorf("%q: status %d, handler ran %d times; want %d and none", c.raw[:20],
				resp.StatusCode, ran.Load(), c.want)
		}
		checkHdrs(t, resp.Header)
	}
}
