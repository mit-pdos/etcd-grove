// Package httphdr is the evidence for respHdrsOk's key and value clauses and for Flush_spec's
// committed-writer premise (Proof/net/http/Boundary.lean; http-boundary-fix, 2026-11-14, the
// independent review's MAJOR 2):
//
//   - TestRewritten: Go's server turns CR/LF in a header value into spaces, its client trims a
//     value's surrounding spaces and tabs, and a key with a non-token byte is not sent, so srvView's
//     "the client sees the handler's value" was false of them.
//   - TestUnchanged: a token key with a value of printable ASCII, not starting or ending with a
//     space (respHdrsOk), reaches the client unchanged, empty values included.
//   - TestFlushCommits: Flush on an uncommitted writer commits status 200; a later WriteHeader is
//     ignored, so Flush_spec now asks for a committed writer.
package httphdr

import (
	"net"
	"net/http"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

func get(t *testing.T, h http.HandlerFunc) *http.Response {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	go http.Serve(l, h)
	rt, err := transport.NewTimeoutTransport(transport.TLSInfo{}, time.Second, 0, 0)
	if err != nil {
		t.Fatal(err)
	}
	req, _ := http.NewRequest(http.MethodGet, "http://"+l.Addr().String()+"/x", nil)
	resp, err := rt.RoundTrip(req)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	return resp
}

func TestRewritten(t *testing.T) {
	set := map[string]string{"X-Nl": "a\nb", "X-Cr": "a\rb", "X-Pad": " pad ", "X-Tab": "\tt\t", "Bad Key": "v"}
	resp := get(t, func(w http.ResponseWriter, r *http.Request) {
		for k, v := range set {
			w.Header().Set(k, v)
		}
		w.WriteHeader(200)
	})
	for k, v := range set {
		if got := resp.Header.Get(k); got == v {
			t.Errorf("%q: %q reached the client unchanged; want Go's rewrite", k, v)
		}
	}
}

func TestUnchanged(t *testing.T) {
	set := map[string]string{"X-Etcd-Cluster-Id": "8e9e05c52164694d", "X-Server-Version": "3.8.0-alpha.0",
		"Allow": "POST", "X-Inner": "a b\x7e!", "X-Empty": ""}
	resp := get(t, func(w http.ResponseWriter, r *http.Request) {
		for k, v := range set {
			w.Header().Set(k, v)
		}
		w.WriteHeader(204)
	})
	for k, v := range set {
		if vs, ok := resp.Header[http.CanonicalHeaderKey(k)]; !ok || vs[0] != v {
			t.Errorf("%q: handler set %q, client sees %q (present %v)", k, v, resp.Header.Get(k), ok)
		}
	}
}

func TestFlushCommits(t *testing.T) {
	resp := get(t, func(w http.ResponseWriter, r *http.Request) {
		w.(http.Flusher).Flush()
		w.Header().Set("X-After", "v")
		w.WriteHeader(500)
	})
	if resp.StatusCode != 200 || resp.Header.Get("X-After") != "" {
		t.Errorf("status %d, X-After %q; want Flush's 200 and no later header", resp.StatusCode, resp.Header.Get("X-After"))
	}
}
