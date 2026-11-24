package server

import (
	"net/url"
	"os"
	"testing"
	"time"

	"golang.org/x/net/http/httpproxy"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// proxyVars are the variables proxyEnvSet reads; the others only turn a proxy off.
var proxyVars = []string{"HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy"}

// clearProxyEnv unsets, for the test, every variable net/http's proxy configuration reads.
func clearProxyEnv(t *testing.T) {
	for _, k := range append(proxyVars, "NO_PROXY", "no_proxy", "REQUEST_METHOD") {
		t.Setenv(k, "")
		os.Unsetenv(k)
	}
}

// peerURL is a member's peer URL as rafthttp dials it (a raft stream path).
var peerURL = &url.URL{Scheme: "http", Host: "10.77.1.1:2380", Path: "/raft/stream/message/1"}

// TestProxyEnvSet: the check is false with no variable set, and true with each one set; and it covers
// what net/http reads: with the check false, httpproxy.FromEnvironment (what http.ProxyFromEnvironment
// reads, once per process) proxies no peer URL, and with each variable set it proxies the peer URL of
// its scheme (non-vacuity: the variables the check reads are the ones that matter).
func TestProxyEnvSet(t *testing.T) {
	clearProxyEnv(t)
	if proxyEnvSet() {
		t.Fatal("proxyEnvSet with no proxy variable set")
	}
	if p, err := httpproxy.FromEnvironment().ProxyFunc()(peerURL); err != nil || p != nil {
		t.Fatalf("no variable set, yet the peer URL is proxied: %v %v", p, err)
	}
	for _, k := range proxyVars {
		t.Run(k, func(t *testing.T) {
			clearProxyEnv(t)
			t.Setenv(k, "http://10.9.9.9:3128")
			if !proxyEnvSet() {
				t.Fatalf("proxyEnvSet false with %s set", k)
			}
			u := *peerURL
			if k == "HTTPS_PROXY" || k == "https_proxy" {
				u.Scheme = "https"
			}
			p, err := httpproxy.FromEnvironment().ProxyFunc()(&u)
			if err != nil || p == nil || p.Host != "10.9.9.9:3128" {
				t.Fatalf("%s set, the %s peer URL not proxied: %v %v", k, u.Scheme, p, err)
			}
		})
	}
}

// TestMainLoggerProxyRefused: with a proxy variable set, MainLogger returns at once, before NewServer
// (it creates no data directory), on a configuration it would otherwise start a member from.
func TestMainLoggerProxyRefused(t *testing.T) {
	clearProxyEnv(t)
	t.Setenv("HTTP_PROXY", "http://10.9.9.9:3128")
	name := "proxyrefused-" + time.Now().Format("150405.000000000")
	c := Config{Name: name, Peer: "127.0.0.1:0", Client: "127.0.0.1:0",
		Cluster: []Peer{{Name: name, Addr: "127.0.0.1:0"}}, Token: "t", SnapCount: 1, CatchUp: 1}
	if !inCluster(c) {
		t.Fatal("the configuration is not one MainLogger would start")
	}
	done := make(chan struct{})
	go func() { Main(c); close(done) }()
	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("MainLogger did not return with HTTP_PROXY set")
	}
	dir := etcdstart.DataBase + "/" + name + ".etcd"
	if _, err := os.Stat(dir); err == nil {
		os.RemoveAll(dir)
		t.Fatalf("MainLogger reached NewServer with HTTP_PROXY set (%s exists)", dir)
	}
}
