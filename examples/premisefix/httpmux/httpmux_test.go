// Package httpmux checks what net/http's ServeMux does with literal path patterns (premise fixes 4,
// fix 3, 2026-11-10), the behavior http.mux_handlerOk_spec (Proof/net/http/Boundary.lean) states:
// a request whose path is not in ServeMux's clean form (method not CONNECT), or whose path p lacks
// a trailing slash while p is no pattern and p+"/" is one, gets a 307 redirect and runs no handler;
// any other request runs the handler of the longest matching pattern (`route`), or gets a 404. Go
// 1.27 redirects with 307 (StatusTemporaryRedirect), not 301 as the statement said until then.
// Found by the round-2 premise attack (http-mux-redirect-307).
package httpmux

import (
	"bufio"
	"fmt"
	"net"
	"net/http"
	"strings"
	"testing"
)

type h struct {
	name string
	got  *string
}

func (x h) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	*x.got = x.name
	w.WriteHeader(200)
}

// do sends one raw request line (so the path reaches the server as written) and returns the status,
// the Location header, and the pattern whose handler ran ("" for none).
func do(t *testing.T, pats []string, method, path string) (int, string, string) {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	got := ""
	m := http.NewServeMux()
	for _, p := range pats {
		m.Handle(p, h{p, &got})
	}
	go http.Serve(l, m)
	c, err := net.Dial("tcp", l.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	fmt.Fprintf(c, "%s %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n", method, path)
	resp, err := http.ReadResponse(bufio.NewReader(c), nil)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	return resp.StatusCode, resp.Header.Get("Location"), got
}

var raftPats = []string{"/raft", "/raft/stream/", "/raft/snapshot", "/raft/probing"}

func TestServeMux(t *testing.T) {
	for _, c := range []struct {
		pats         []string
		method, path string
		status       int
		loc, handler string
	}{
		// clean and routed: the longest matching pattern's handler
		{raftPats, "GET", "/raft", 200, "", "/raft"},
		{raftPats, "POST", "/raft/stream/msgapp/1", 200, "", "/raft/stream/"},
		{raftPats, "POST", "/raft/snapshot", 200, "", "/raft/snapshot"},
		{[]string{"/a/", "/a/b/"}, "GET", "/a/b/c", 200, "", "/a/b/"},
		{[]string{"/a/"}, "GET", "/a/b", 200, "", "/a/"},
		// clean, routed nowhere: 404
		{raftPats, "GET", "/raft/x", 404, "", ""},
		{raftPats, "GET", "/", 404, "", ""},
		// the trailing-slash redirect: p not a pattern, p+"/" one: 307, no handler
		{raftPats, "GET", "/raft/stream", 307, "/raft/stream/", ""},
		{[]string{"/a/", "/a/b/"}, "GET", "/a/b", 307, "/a/b/", ""},
		{[]string{"/a/"}, "GET", "/a", 307, "/a/", ""},
		// not clean (an empty, `.` or `..` segment): 307 to the clean path, no handler, even where
		// `route` of the raw path would find a pattern
		{[]string{"/a/"}, "GET", "/a/./b", 307, "/a/b", ""},
		{[]string{"/a/"}, "GET", "/a//b", 307, "/a/b", ""},
		{[]string{"/a/"}, "GET", "/a/b/../c", 307, "/a/c", ""},
		{raftPats, "POST", "/raft/stream/../snapshot", 307, "/raft/snapshot", ""},
		// ... but a CONNECT request's path is not cleaned: routed as it is
		{[]string{"/a/"}, "CONNECT", "/a//b", 200, "", "/a/"},
		{[]string{"/a/"}, "CONNECT", "/a", 307, "/a/", ""},
	} {
		st, loc, hd := do(t, c.pats, c.method, c.path)
		if st != c.status || loc != c.loc || hd != c.handler {
			t.Errorf("pats=%q %s %q: got status %d, Location %q, handler %q; want %d, %q, %q",
				c.pats, c.method, c.path, st, loc, hd, c.status, c.loc, c.handler)
		}
		if st == 301 || strings.Contains(loc, "://") {
			t.Errorf("unexpected: %d %q", st, loc)
		}
	}
}
