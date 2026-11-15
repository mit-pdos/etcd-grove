// Package httpgzip is the evidence for respHdrsOk's Content-Encoding clause (Proof/net/http/
// Boundary.lean, hdrsReady; http-boundary-fix, 2026-11-14, the independent review's MAJOR 1):
// rafthttp's round trippers (transport.NewTimeoutTransport) leave compression on, so a response
// whose handler set Content-Encoding: gzip reaches the client decompressed, its reads not a
// prefix of what the handler wrote (respReader, ReadFull_resp_spec), with the header gone
// (srvView). Without the header, the client reads the handler's bytes.
package httpgzip

import (
	"bytes"
	"compress/gzip"
	"io"
	"net"
	"net/http"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

func TestTransparentGunzip(t *testing.T) {
	var G bytes.Buffer
	zw := gzip.NewWriter(&G)
	zw.Write([]byte("hello"))
	zw.Close()
	g := G.Bytes()
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/gz" {
			w.Header().Set("Content-Encoding", "gzip")
		}
		w.WriteHeader(200)
		w.Write(g)
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
	read := func(path string) ([]byte, http.Header) {
		req, _ := http.NewRequest(http.MethodPost, "http://"+l.Addr().String()+path, bytes.NewBufferString("m"))
		resp, err := rt.RoundTrip(req)
		if err != nil {
			t.Fatal(err)
		}
		b, err := io.ReadAll(resp.Body)
		if err != nil {
			t.Fatal(err)
		}
		return b, resp.Header
	}
	if b, hd := read("/gz"); string(b) != "hello" || hd.Get("Content-Encoding") != "" {
		t.Errorf("with Content-Encoding: read %q, header %q; want Go's decompression", b, hd.Get("Content-Encoding"))
	}
	if b, _ := read("/plain"); !bytes.Equal(b, g) {
		t.Errorf("without Content-Encoding: read % x, want the handler's bytes", b)
	}
}
