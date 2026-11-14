// Package httpreplay checks the http-boundary fix of 2026-11-14 (finding 1 of the network fault
// review): one RoundTrip of a replayable request can run the server's handler twice, so the
// request's exclusive ticket (http.reqTicket, Proof/net/http/Boundary.lean) may go only to the
// handler of a request Go never replays (http.onceOnly, http.reqTicketOnce in handlerOk and
// handlerFor).
//
//   - The old statement's refutation (TestGETRunsHandlerTwice): rafthttp's round tripper
//     (NewRoundTripper is transport.NewTimeoutTransport(tlsInfo, dt, 0, 0)) replays a GET whose
//     response read fails on a reused connection: one RoundTrip, two handler runs. handlerOk gave
//     each run reqTicket γk of the one ticket name: two copies of an exclusive resource.
//   - The idempotency key (TestIdempotencyKeyPOSTRunsHandlerTwice): a POST of a rewindable body
//     (NewRequest of a *strings.Reader sets GetBody) with Idempotency-Key or X-Idempotency-Key
//     present, even with an empty value, is replayed too (Request.isReplayable tests presence):
//     onceOnly asks for neither key (http.noIdemKey), whatever its value.
//   - The new statement (TestPOSTRunsHandlerOnce): a POST without an idempotency key, as rafthttp's
//     pipeline and snapshot senders send them (createPostRequest), is never replayed: the RoundTrip
//     fails and the handler ran once.
package httpreplay

import (
	"net"
	"net/http"
	"strings"
	"sync"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

// runs sends a first request (which leaves an idle connection to reuse), then a second whose
// first handler run aborts (as a connection breaking before the response), and returns how many
// times the handler ran for the second and the second RoundTrip's error.
func runs(t *testing.T, mk func(url, nonce string) *http.Request) (int, error) {
	t.Helper()
	var mu sync.Mutex
	count := map[string]int{}
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		n := r.Header.Get("Nonce")
		mu.Lock()
		count[n]++
		c := count[n]
		mu.Unlock()
		if n == "second" && c == 1 {
			panic(http.ErrAbortHandler) // Serve recovers it and drops the connection: no response
		}
		w.WriteHeader(200)
	})
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go http.Serve(l, h)
	rt, err := transport.NewTimeoutTransport(transport.TLSInfo{}, time.Second, 0, 0)
	if err != nil {
		t.Fatal(err)
	}
	var last error
	for _, n := range []string{"first", "second"} {
		resp, err := rt.RoundTrip(mk("http://"+l.Addr().String()+"/raft", n))
		if err == nil {
			resp.Body.Close()
		}
		last = err
	}
	mu.Lock()
	defer mu.Unlock()
	return count["second"], last
}

func TestGETRunsHandlerTwice(t *testing.T) {
	n, err := runs(t, func(u, nonce string) *http.Request {
		req, _ := http.NewRequest(http.MethodGet, u, nil)
		req.Header.Set("Nonce", nonce)
		return req
	})
	if n != 2 || err != nil {
		t.Errorf("one GET RoundTrip: %d handler runs, err %v; want 2 runs and a response", n, err)
	}
}

func TestIdempotencyKeyPOSTRunsHandlerTwice(t *testing.T) {
	for _, k := range []string{"Idempotency-Key", "X-Idempotency-Key", "idempotency-key"} {
		for _, v := range []string{"", "k1"} {
			n, err := runs(t, func(u, nonce string) *http.Request {
				req, _ := http.NewRequest(http.MethodPost, u, strings.NewReader("body"))
				req.Header.Set("Nonce", nonce)
				req.Header.Set(k, v)
				return req
			})
			if n != 2 || err != nil {
				t.Errorf("POST with %s: %q: %d handler runs, err %v; want 2 runs", k, v, n, err)
			}
		}
	}
}

func TestPOSTRunsHandlerOnce(t *testing.T) {
	n, err := runs(t, func(u, nonce string) *http.Request {
		req, _ := http.NewRequest(http.MethodPost, u, strings.NewReader("body"))
		req.Header.Set("Nonce", nonce)
		req.Header.Set("Content-Type", "application/protobuf")
		req.Header.Set("X-Server-From", "1")
		req.Header.Set("X-Server-Version", "3.8.0")
		req.Header.Set("X-Min-Cluster-Version", "3.0.0")
		req.Header.Set("X-Etcd-Cluster-ID", "1000")
		req.Header.Set("X-PeerURLs", "http://127.0.0.1:2380")
		return req
	})
	if n != 1 || err == nil {
		t.Errorf("one POST RoundTrip: %d handler runs, err %v; want 1 run and an error", n, err)
	}
}
