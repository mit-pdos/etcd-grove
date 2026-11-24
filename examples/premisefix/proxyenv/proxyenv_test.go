// Package proxyenv is the Go evidence for the planned premise `proxyEnvOff` (etcd-dist, 2026-11-23;
// added when phase 7 S5's HTTP client reads the variables, notes/putget-dist-plan.md section 11): in a run where none of the six variables
// HTTP_PROXY, http_proxy, HTTPS_PROXY, https_proxy, NO_PROXY, no_proxy has a non-empty value (and
// no code of the run sets them), os.Getenv returns "" for each of them, so
// golang.org/x/net/http/httpproxy's FromEnvironment (Go's http.ProxyFromEnvironment, and grpc-go's
// proxy lookup) gives no proxy for any URL, loopback or not, whatever REQUEST_METHOD is. Where one
// of them is set, a non-loopback request is proxied: net/http's Transport and grpc-go's dialer then
// connect to the proxy, not to the member, which is why a distributed deployment (members at
// non-loopback addresses, `Net.addrOk`) needs the premise where the single-process theorems got by
// with loopback literals (`netAddrLit`, examples/premisefix/httpproxy).
//
// Each case runs in a child process (the test binary itself, PROXYENV_CHILD set), since
// http.ProxyFromEnvironment reads the environment once per process.
package proxyenv

import (
	"bufio"
	"context"
	"fmt"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
)

var proxyKeys = []string{"HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "NO_PROXY", "no_proxy"}

// Non-loopback member addresses of the shape the distributed harness uses (TestDist: 10.77.k.1).
const peerURL, clientURL = "http://10.77.1.1:2380", "https://10.77.1.1:2379"

func TestMain(m *testing.M) {
	switch os.Getenv("PROXYENV_CHILD") {
	case "":
		os.Exit(m.Run())
	case "http":
		childHTTP()
	case "grpc":
		childGRPC()
	}
	os.Exit(0)
}

// childHTTP prints the six variables as os.Getenv reads them, then ProxyFromEnvironment's answer
// for the peer URL (http) and the client URL (https).
func childHTTP() {
	for _, k := range proxyKeys {
		fmt.Printf("getenv %s=%q\n", k, os.Getenv(k))
	}
	for _, s := range []string{peerURL, clientURL} {
		u, _ := url.Parse(s)
		p, err := http.ProxyFromEnvironment(&http.Request{URL: u})
		fmt.Printf("proxy %s %v %v\n", s, p, err)
	}
}

// childGRPC dials a non-loopback target with grpc-go and makes one call; whether a proxy saw a
// CONNECT is reported by the parent.
func childGRPC() {
	cc, err := grpc.NewClient("passthrough:///10.77.1.1:2379",
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		fmt.Println("newclient", err)
		return
	}
	defer cc.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	err = cc.Invoke(ctx, "/etcdserverpb.KV/Range", &struct{}{}, &struct{}{})
	fmt.Println("invoke", err != nil)
}

// child runs the test binary in mode with exactly env's proxy variables (the others removed).
func child(t *testing.T, mode string, env map[string]string) string {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	for _, kv := range os.Environ() {
		k, _, _ := strings.Cut(kv, "=")
		drop := k == "REQUEST_METHOD"
		for _, p := range proxyKeys {
			drop = drop || k == p
		}
		if !drop {
			cmd.Env = append(cmd.Env, kv)
		}
	}
	cmd.Env = append(cmd.Env, "PROXYENV_CHILD="+mode)
	for k, v := range env {
		cmd.Env = append(cmd.Env, k+"="+v)
	}
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("child %s: %v\n%s", mode, err, out)
	}
	return string(out)
}

func noProxy(out string) bool {
	return strings.Contains(out, "proxy "+peerURL+" <nil> <nil>") &&
		strings.Contains(out, "proxy "+clientURL+" <nil> <nil>")
}

// TestProxyEnvOff: under the premise (each variable unset, or set to ""), os.Getenv reads "" for
// each and no URL is proxied, with or without REQUEST_METHOD (CGI).
func TestProxyEnvOff(t *testing.T) {
	empty := map[string]string{}
	for _, k := range proxyKeys {
		empty[k] = ""
	}
	cases := map[string]map[string]string{
		"unset":                {},
		"empty":                empty,
		"unset, CGI":           {"REQUEST_METHOD": "GET"},
		"empty, NO_PROXY=\"\"": {"NO_PROXY": "", "no_proxy": ""},
	}
	for name, env := range cases {
		out := child(t, "http", env)
		for _, k := range proxyKeys {
			if !strings.Contains(out, fmt.Sprintf("getenv %s=%q", k, "")) {
				t.Errorf("%s: os.Getenv(%s) not \"\":\n%s", name, k, out)
			}
		}
		if !noProxy(out) {
			t.Errorf("%s: a URL is proxied:\n%s", name, out)
		}
		t.Logf("%s: every proxy variable reads \"\", no URL proxied", name)
	}
}

// TestProxyEnvOn: each variable that names a proxy (the premise violated) proxies the matching
// scheme of a non-loopback URL; NO_PROXY alone proxies nothing (the premise is stronger than
// needed there, kept for one uniform statement).
func TestProxyEnvOn(t *testing.T) {
	for _, c := range []struct {
		k, want string
	}{
		{"HTTP_PROXY", peerURL}, {"http_proxy", peerURL},
		{"HTTPS_PROXY", clientURL}, {"https_proxy", clientURL},
	} {
		out := child(t, "http", map[string]string{c.k: "http://127.0.0.1:3128"})
		if !strings.Contains(out, "proxy "+c.want+" http://127.0.0.1:3128 <nil>") {
			t.Errorf("%s set: %s not proxied:\n%s", c.k, c.want, out)
		}
		t.Logf("%s set: %s proxied (premise violated)", c.k, c.want)
	}
	if out := child(t, "http", map[string]string{"NO_PROXY": "*"}); !noProxy(out) {
		t.Errorf("NO_PROXY alone proxies:\n%s", out)
	}
}

// TestGrpcProxy: grpc-go v1.84 (etcd's clientv3 transport) sends a non-loopback dial to the proxy
// HTTPS_PROXY names (an HTTP CONNECT), and dials directly when no proxy variable is set.
func TestGrpcProxy(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	seen := make(chan string, 4)
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			line, _ := bufio.NewReader(c).ReadString('\n')
			seen <- strings.TrimSpace(line)
			c.Close()
		}
	}()
	child(t, "grpc", map[string]string{"HTTPS_PROXY": "http://" + l.Addr().String()})
	select {
	case line := <-seen:
		if !strings.HasPrefix(line, "CONNECT 10.77.1.1:2379") {
			t.Errorf("proxy saw %q, want a CONNECT to the member", line)
		}
		t.Logf("HTTPS_PROXY set: grpc's dial went to the proxy: %q", line)
	case <-time.After(5 * time.Second):
		t.Errorf("HTTPS_PROXY set: no CONNECT reached the proxy")
	}
	child(t, "grpc", map[string]string{})
	select {
	case line := <-seen:
		t.Errorf("no proxy variable: the proxy still saw %q", line)
	default:
		t.Logf("no proxy variable: grpc dialed directly (the proxy saw nothing)")
	}
}
