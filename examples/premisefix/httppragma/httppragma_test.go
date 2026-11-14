// Package httppragma is the evidence for the Pragma/Cache-Control exclusions of the HTTP
// boundary's header views (Proof/net/http/Boundary.lean: Pragma in respNoKeys, Cache-Control in
// reqTpKeys; http-boundary-fix, second review, 2026-11-14): Go adds Cache-Control: no-cache to a
// header map it reads with Pragma: no-cache and no Cache-Control (fixPragmaCacheControl, go1.27.3
// net/http/response.go:218, called by readRequest, request.go:1177, and ReadResponse,
// response.go:201), on the server for a request and on the client for a response.
package httppragma

import (
	"net"
	"net/http"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

func TestPragmaAddsCacheControl(t *testing.T) {
	got := make(chan http.Header, 1)
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		got <- r.Header.Clone()
		w.Header().Set("Pragma", "no-cache")
		w.WriteHeader(204)
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
	req, _ := http.NewRequest(http.MethodGet, "http://"+l.Addr().String()+"/x", nil)
	req.Header.Set("Pragma", "no-cache")
	resp, err := rt.RoundTrip(req)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if sh := <-got; sh.Get("Cache-Control") != "no-cache" {
		t.Errorf("server: Cache-Control %q; want Go's no-cache", sh.Get("Cache-Control"))
	}
	if resp.Header.Get("Cache-Control") != "no-cache" {
		t.Errorf("client: Cache-Control %q; want Go's no-cache", resp.Header.Get("Cache-Control"))
	}
}
