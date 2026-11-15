// Package httpproxy is the evidence for netAddrLit's loopback restriction (Proof/net/InvNet.lean,
// http-boundary-fix, 2026-11-14): rafthttp's round trippers (transport.NewTimeoutTransport, an
// *http.Transport with Proxy: http.ProxyFromEnvironment) send a request to a non-loopback IPv4
// literal through the proxy HTTP_PROXY names, which may answer itself (here 502) with a status
// neither a handler nor Go's server made, so roundTripperOk's promise of the protocol's resp is
// false of it; a request to a 127.0.0.0/8 literal is never proxied (go1.27.3
// vendor/golang.org/x/net/http/httpproxy/proxy.go, useProxy).
package httpproxy

import (
	"net"
	"net/http"
	"sync/atomic"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

func TestProxyOnlyNonLoopback(t *testing.T) {
	var proxied atomic.Int32
	proxy := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		proxied.Add(1)
		w.WriteHeader(http.StatusBadGateway) // the proxy's own answer
	})
	pl, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer pl.Close()
	go http.Serve(pl, proxy)
	t.Setenv("HTTP_PROXY", "http://"+pl.Addr().String())
	t.Setenv("NO_PROXY", "")
	t.Setenv("http_proxy", "")
	t.Setenv("no_proxy", "")

	member := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { w.WriteHeader(204) })
	ml, err := net.Listen("tcp", "127.0.0.2:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ml.Close()
	go http.Serve(ml, member)

	// The transport reads the environment once per process (envProxyFunc): make it after Setenv.
	rt, err := transport.NewTimeoutTransport(transport.TLSInfo{}, time.Second, 0, 0)
	if err != nil {
		t.Fatal(err)
	}
	get := func(u string) int {
		req, _ := http.NewRequest(http.MethodGet, u, nil)
		resp, err := rt.RoundTrip(req)
		if err != nil {
			t.Fatalf("%s: %v", u, err)
		}
		resp.Body.Close()
		return resp.StatusCode
	}
	if st := get("http://" + ml.Addr().String() + "/raft/stream/message/1"); st != 204 || proxied.Load() != 0 {
		t.Errorf("loopback 127.0.0.2: status %d, proxied %d times; want 204 and none", st, proxied.Load())
	}
	if st := get("http://10.255.255.1:2380/raft/stream/message/1"); st != 502 || proxied.Load() != 1 {
		t.Errorf("non-loopback 10.255.255.1: status %d, proxied %d times; want the proxy's 502", st, proxied.Load())
	}
}
