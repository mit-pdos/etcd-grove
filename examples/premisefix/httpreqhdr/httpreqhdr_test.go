// Package httpreqhdr is the evidence for reqAt's header clause (reqHdrView, Proof/net/http/
// Boundary.lean; http-boundary-fix, 2026-11-14, the independent review's MAJOR 1 and 2, request
// side): through rafthttp's round trippers, the handler sees headers the client did not set
// (Accept-Encoding, User-Agent, Content-Length: reqTpKeys) and the client's values trimmed of
// surrounding spaces and tabs; a key with a non-token byte or a value with CR or LF makes
// RoundTrip fail; every other key reaches the handler with the client's value.
package httpreqhdr

import (
	"net"
	"net/http"
	"strings"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

func TestRequestHeaders(t *testing.T) {
	got := make(chan http.Header, 1)
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { got <- r.Header.Clone(); w.WriteHeader(204) })
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
	send := func(hs map[string]string) (http.Header, error) {
		req, _ := http.NewRequest(http.MethodPost, "http://"+l.Addr().String()+"/raft", strings.NewReader("xyz"))
		for k, v := range hs {
			req.Header.Set(k, v)
		}
		resp, err := rt.RoundTrip(req)
		if err != nil {
			return nil, err
		}
		resp.Body.Close()
		return <-got, nil
	}
	// the keys the transport sets, and trimming
	sh, err := send(map[string]string{"X-Server-From": "8e9e05c52164694d", "X-Pad": " pad ", "X-Tab": "\tt\t", "X-Empty": ""})
	if err != nil {
		t.Fatal(err)
	}
	for _, k := range []string{"Accept-Encoding", "User-Agent", "Content-Length"} {
		if sh.Get(k) == "" {
			t.Errorf("%s: the handler sees no value; want the transport's", k)
		}
	}
	for k, want := range map[string]string{"X-Server-From": "8e9e05c52164694d", "X-Pad": "pad", "X-Tab": "t"} {
		if sh.Get(k) != want {
			t.Errorf("%s: the handler sees %q, want %q", k, sh.Get(k), want)
		}
	}
	if vs, ok := sh["X-Empty"]; !ok || vs[0] != "" {
		t.Errorf("X-Empty: present %v", ok)
	}
	// refused by the client
	for _, hs := range []map[string]string{{"Bad Key": "v"}, {"X-Nl": "a\nb"}, {"X-Cr": "a\rb"}} {
		if _, err := send(hs); err == nil {
			t.Errorf("%q: RoundTrip succeeded; want the client's refusal", hs)
		}
	}
}
