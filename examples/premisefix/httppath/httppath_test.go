// Package httppath checks that a request built as rafthttp builds them (http.NewRequest of
// url.URL{Scheme: "http", Host: host, Path: path}.String(), sent by an http.Transport) reaches the
// server's handler with r.URL.Path == path exactly when path starts with '/' (premise fixes 4,
// fix 4, 2026-11-10): reqAt (Proof/net/http/Boundary.lean) gives the handler the client's path, and
// NewRequest_spec now asks for a path starting with '/'. Go sends "" as "/" and "a" as "/a". Found
// by the round-2 premise attack (http-reqAt-path-not-slash).
package httppath

import (
	"net"
	"net/http"
	"net/url"
	"testing"
)

type rec struct{ got chan string }

func (x rec) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	x.got <- r.URL.Path
	w.WriteHeader(200)
}

func seen(t *testing.T, method, path string) string {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	h := rec{make(chan string, 1)}
	go http.Serve(l, h)
	u := (&url.URL{Scheme: "http", Host: l.Addr().String(), Path: path}).String()
	req, err := http.NewRequest(method, u, nil)
	if err != nil {
		t.Fatal(err)
	}
	resp, err := (&http.Transport{}).RoundTrip(req)
	if err != nil {
		t.Fatalf("path %q: %v", path, err)
	}
	resp.Body.Close()
	return <-h.got
}

func TestPathKept(t *testing.T) {
	for _, p := range []string{"/", "/raft", "/raft/stream/msgapp/8e9e05c52164694d", "/raft/snapshot",
		"//a", "///a", "/a//b", "/a/./b", "/a/../b", "/a/", "/a b", "/a%2Fb", "/a?b", "/a#b", "/a;b",
		"/é", "/\x01", "/a\tb", "/%", "/a+b", "/~a", "/\xff", "/a\x00b", "/\x7f", "/a\r\nb"} {
		for _, m := range []string{"GET", "POST"} {
			if got := seen(t, m, p); got != p {
				t.Errorf("%s path %q: the handler saw %q", m, p, got)
			}
		}
	}
}

func TestPathWithoutSlashChanged(t *testing.T) {
	for _, c := range []struct{ path, want string }{{"", "/"}, {"a", "/a"}, {"a/b", "/a/b"}} {
		if got := seen(t, "GET", c.path); got != c.want {
			t.Errorf("path %q: the handler saw %q, want %q", c.path, got, c.want)
		}
	}
}
