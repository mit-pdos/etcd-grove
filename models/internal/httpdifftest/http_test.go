// Package httpdifftest holds the differential tests of the net/http model (models/net/http):
// run.sh (models/internal/rpcdifftest/run.sh) runs them against Go's real net/http and against
// the model (`go test -overlay`, models/goroot.py, tag netmodel). Each test computes a
// transcript of what a program observes (the raw bytes a server answers raw requests with; what
// ReadRequest and ReadResponse return on raw heads and their mutations) and compares it with the
// golden one in testdata/, which only the real build writes (`go test -update`). In the model's
// transcript an entry may instead be "NOT MODELLED" (the model blocked forever: a not-modelled point,
// which stands for no behavior), never another value.
package httpdifftest

import (
	"bufio"
	"bytes"
	"flag"
	"fmt"
	"io"
	"math/rand"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"testing"
	"time"

	"models.lab/internal/stuck"
)

var update = flag.Bool("update", false, "write the golden transcripts (real build only)")

// golden compares got with testdata/name (or writes it, with -update in the real build).
// Entries are separated by "\n=== "; the model may answer "NOT MODELLED" for an entry.
func golden(t *testing.T, name, got string) {
	t.Helper()
	p := filepath.Join("testdata", name)
	if *update {
		if model {
			t.Fatal("-update writes the real build's transcript; run it without the model")
		}
		os.MkdirAll("testdata", 0o755)
		if err := os.WriteFile(p, []byte(got), 0o644); err != nil {
			t.Fatal(err)
		}
		return
	}
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatalf("%v (run go test -update in the real build)", err)
	}
	want := strings.Split(string(b), "\n=== ")
	have := strings.Split(got, "\n=== ")
	if len(want) != len(have) {
		t.Fatalf("%s: %d entries, the golden transcript has %d", name, len(have), len(want))
	}
	nm := 0
	for i := range want {
		wh, _, _ := strings.Cut(want[i], "\n")
		hh, hrest, _ := strings.Cut(have[i], "\n")
		if wh != hh {
			t.Fatalf("%s: entry %d is %q, the golden one %q", name, i, hh, wh)
		}
		if model && hrest == "NOT MODELLED" {
			nm++
			continue
		}
		if want[i] != have[i] {
			t.Errorf("%s: entry %q differs:\n--- golden (real)\n%s\n--- this build\n%s", name, wh, want[i], have[i])
		}
	}
	if nm > 0 {
		t.Logf("%s: %d of %d entries not modelled", name, nm, len(want))
	}
}

// handler answers by path; /echo describes the request it got.
func handler(w http.ResponseWriter, r *http.Request) {
	switch r.URL.Path {
	case "/big":
		w.Write(bytes.Repeat([]byte("x"), 5000))
	case "/flush":
		w.Write([]byte("a"))
		w.(http.Flusher).Flush()
		w.Write([]byte("b"))
	case "/notfound":
		http.NotFound(w, r)
	case "/html":
		w.Write([]byte("<html><body>hi</body></html>"))
	case "/setlen":
		w.Header().Set("Content-Length", "3")
		w.Write([]byte("abc"))
	case "/hijack":
		c, bufrw, err := w.(http.Hijacker).Hijack()
		if err != nil {
			panic(err)
		}
		fmt.Fprintf(c, "HIJACKED buffered=%d\n", bufrw.Reader.Buffered())
		c.Close()
	case "/redirect":
		http.Redirect(w, r, "/echo?x=1", http.StatusFound)
	case "/twice":
		w.WriteHeader(201)
		w.WriteHeader(202)
	case "/ctx":
		select {
		case <-r.Context().Done():
			w.Write([]byte("ctx done"))
		default:
			w.Write([]byte("ctx live"))
		}
	default:
		body, err := io.ReadAll(r.Body)
		var hs []string
		for k, vs := range r.Header {
			hs = append(hs, fmt.Sprintf("%s=%q", k, vs))
		}
		sort.Strings(hs)
		w.Header().Set("Content-Type", "text/plain")
		fmt.Fprintf(w, "method=%s uri=%q path=%q query=%q proto=%s host=%q close=%v len=%d te=%v\n"+
			"headers=%s\nbody=%q err=%v\n", r.Method, r.RequestURI, r.URL.Path, r.URL.RawQuery,
			r.Proto, r.Host, r.Close, r.ContentLength, r.TransferEncoding, strings.Join(hs, " "), body, err)
	}
}

var dateRE = regexp.MustCompile(`(?m)^Date: [^\r]*\r$`)

// exchange writes each of reqs (in turn, or all at once if together) on a new connection to
// addr and returns the bytes the server sent until it closed the connection or went quiet.
func exchange(t *testing.T, addr string, reqs []string, together bool) string {
	c, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var out bytes.Buffer
	read := func(quiet time.Duration) bool {
		buf := make([]byte, 4096)
		for {
			c.SetReadDeadline(time.Now().Add(quiet))
			n, err := c.Read(buf)
			out.Write(buf[:n])
			if err != nil {
				if ne, ok := err.(net.Error); ok && ne.Timeout() {
					return true
				}
				out.WriteString("<EOF>")
				return false
			}
		}
	}
	if together {
		io.WriteString(c, strings.Join(reqs, ""))
		read(300 * time.Millisecond)
	} else {
		for _, r := range reqs {
			io.WriteString(c, r)
			if !read(300 * time.Millisecond) {
				break
			}
		}
	}
	return dateRE.ReplaceAllString(out.String(), "Date: DATE\r")
}

func serve(t *testing.T, srv *http.Server) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	go srv.Serve(l)
	t.Cleanup(func() { srv.Close() })
	return l.Addr().String()
}

const host = "Host: h\r\n"

// The server's answers to raw requests, all inside the model (no chunked request body, no
// header continuation line, no space in a header name).
func TestServer(t *testing.T) {
	addr := serve(t, &http.Server{Handler: http.HandlerFunc(handler), ErrorLog: quietLog()})
	cases := []struct {
		name     string
		reqs     []string
		together bool
	}{
		{"get", []string{"GET /echo HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"get-lf", []string{"GET /echo?a=b HTTP/1.1\nHost: h\n\n"}, false},
		{"http10", []string{"GET /echo HTTP/1.0\r\n\r\n"}, false},
		{"http10-keepalive", []string{"GET /echo HTTP/1.0\r\nConnection: keep-alive\r\n\r\n",
			"GET /echo HTTP/1.0\r\n\r\n"}, false},
		{"keepalive", []string{"GET /echo HTTP/1.1\r\n" + host + "\r\n", "GET /notfound HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"pipelined", []string{"GET /echo HTTP/1.1\r\n" + host + "\r\n", "HEAD /echo HTTP/1.1\r\n" + host + "\r\n"}, true},
		{"close", []string{"GET /echo HTTP/1.1\r\n" + host + "Connection: close\r\n\r\n"}, false},
		{"headers", []string{"GET /echo HTTP/1.1\r\n" + host + "x-lower: a\r\nX-Two: 1\r\nx-two: 2\r\n" +
			"Spaced:   v  \r\nTabbed:\tv\t\r\nEmpty:\r\nObs: caf\xc3\xa9\r\nWeird!#$%&'*+-.^_`|~Name: z\r\n\r\n"}, false},
		{"header-cr", []string{"GET /echo HTTP/1.1\r\n" + host + "Cr: v\r\r\n\r\n"}, false},
		{"post", []string{"POST /echo HTTP/1.1\r\n" + host + "Content-Length: 5\r\n\r\nhello"}, false},
		{"post-keepalive", []string{"POST /echo HTTP/1.1\r\n" + host + "Content-Length: 3\r\n\r\nabc",
			"GET /echo HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"post-unread", []string{"POST /notfound HTTP/1.1\r\n" + host + "Content-Length: 4\r\n\r\nabcd",
			"GET /echo HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"post-crlf-tolerance", []string{"POST /echo HTTP/1.1\r\n" + host + "Content-Length: 1\r\n\r\nx",
			"\r\nGET /echo HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"expect-continue", []string{"POST /echo HTTP/1.1\r\n" + host + "Expect: 100-continue\r\nContent-Length: 2\r\n\r\n", "ok"}, false},
		{"expect-other", []string{"POST /echo HTTP/1.1\r\n" + host + "Expect: foo\r\nContent-Length: 2\r\n\r\nok"}, false},
		{"head", []string{"HEAD /big HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"big", []string{"GET /big HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"big-http10", []string{"GET /big HTTP/1.0\r\n\r\n"}, false},
		{"flush", []string{"GET /flush HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"html-sniff", []string{"GET /html HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"setlen", []string{"GET /setlen HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"redirect", []string{"GET /redirect HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"twice", []string{"GET /twice HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"ctx", []string{"GET /ctx HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"hijack", []string{"GET /hijack HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"hijack-buffered", []string{"GET /hijack HTTP/1.1\r\n" + host + "\r\nEXTRA"}, true},
		{"connect-path", []string{"CONNECT /echo HTTP/1.0\r\n\r\n"}, false},
		{"connect-authority", []string{"CONNECT example.com:443 HTTP/1.1\r\n\r\n"}, false},
		{"absolute-uri", []string{"GET http://other/echo HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"options-star", []string{"OPTIONS * HTTP/1.1\r\n" + host + "\r\n"}, false},
		// malformed: Go's 400s (and 431, 501, 505)
		{"no-host", []string{"GET /echo HTTP/1.1\r\n\r\n"}, false},
		{"two-hosts", []string{"GET /echo HTTP/1.1\r\n" + host + host + "\r\n"}, false},
		{"bad-host", []string{"GET /echo HTTP/1.1\r\nHost: a b\r\n\r\n"}, false},
		{"bad-line", []string{"GARBAGE\r\n\r\n"}, false},
		{"bad-method", []string{"G(T / HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"bad-version", []string{"GET / HTTP/x\r\n" + host + "\r\n"}, false},
		{"http2-version", []string{"GET / HTTP/2.0\r\n" + host + "\r\n"}, false},
		{"bad-uri", []string{"GET %zz HTTP/1.1\r\n" + host + "\r\n"}, false},
		{"no-colon", []string{"GET /echo HTTP/1.1\r\n" + host + "NoColon\r\n\r\n"}, false},
		{"bad-name", []string{"GET /echo HTTP/1.1\r\n" + host + "Bad(Name: v\r\n\r\n"}, false},
		{"empty-name", []string{"GET /echo HTTP/1.1\r\n" + host + ": v\r\n\r\n"}, false},
		{"bad-value", []string{"GET /echo HTTP/1.1\r\n" + host + "X: a\x01b\r\n\r\n"}, false},
		{"bad-length", []string{"POST /echo HTTP/1.1\r\n" + host + "Content-Length: x\r\n\r\n"}, false},
		{"two-lengths", []string{"POST /echo HTTP/1.1\r\n" + host + "Content-Length: 1\r\nContent-Length: 2\r\n\r\nab"}, false},
		{"same-lengths", []string{"POST /echo HTTP/1.1\r\n" + host + "Content-Length: 2\r\nContent-Length: 2\r\n\r\nab"}, false},
		{"unsupported-te", []string{"POST /echo HTTP/1.1\r\n" + host + "Transfer-Encoding: gzip\r\n\r\n"}, false},
		{"too-many-headers", []string{"GET /echo HTTP/1.1\r\n" + host + strings.Repeat("X: y\r\n", 600) + "\r\n"}, false},
		{"truncated", []string{"GET /echo HTTP/1.1\r\n" + host}, false},
		{"eof-in-line", []string{"GET /echo HT"}, false},
	}
	var out strings.Builder
	for i, c := range cases {
		if i > 0 {
			out.WriteString("\n=== ")
		}
		fmt.Fprintf(&out, "%s\n%q", c.name, exchange(t, addr, c.reqs, c.together))
	}
	golden(t, "server.golden", out.String())
}

// A header larger than the server's limit: 431.
func TestServerHeaderTooLarge(t *testing.T) {
	addr := serve(t, &http.Server{Handler: http.HandlerFunc(handler), MaxHeaderBytes: 100, ErrorLog: quietLog()})
	got := exchange(t, addr, []string{"GET /echo HTTP/1.1\r\n" + host + "X: " + strings.Repeat("y", 5000) + "\r\n\r\n"}, false)
	golden(t, "toolarge.golden", "toolarge\n"+fmt.Sprintf("%q", got))
}

// A client that goes away while its handler runs: the request's context is canceled (the
// server's background read sees the end of the connection).
func TestServerClientGone(t *testing.T) {
	done := make(chan string, 1)
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		select {
		case <-r.Context().Done():
			done <- "canceled: " + r.Context().Err().Error()
		case <-time.After(5 * time.Second):
			done <- "not canceled"
		}
	})
	addr := serve(t, &http.Server{Handler: h, ErrorLog: quietLog()})
	c, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	io.WriteString(c, "GET / HTTP/1.1\r\n"+host+"\r\n")
	time.Sleep(100 * time.Millisecond)
	c.Close()
	if got := <-done; got != "canceled: context canceled" {
		t.Fatalf("handler of a gone client: %s", got)
	}
}

// heads: a corpus of request and response heads, and seeded mutations of them.
func heads(seed int64, base []string, n int) []string {
	r := rand.New(rand.NewSource(seed))
	out := append([]string(nil), base...)
	ins := []string{" ", "\t", ":", "\r", "\n", "\r\n", "\x01", "\x7f", "\xc3\xa9", "a", "-", "\r\n\r\n", "(", "0", "9"}
	for i := 0; i < n; i++ {
		s := []byte(base[r.Intn(len(base))])
		for k := r.Intn(3); k >= 0; k-- {
			p := r.Intn(len(s) + 1)
			switch r.Intn(3) {
			case 0: // insert
				x := ins[r.Intn(len(ins))]
				s = append(s[:p], append([]byte(x), s[p:]...)...)
			case 1: // delete
				if p < len(s) {
					s = append(s[:p], s[p+1:]...)
				}
			case 2: // truncate
				s = s[:p]
			}
		}
		out = append(out, string(s))
	}
	return out
}

// try runs f, returning "NOT MODELLED" if the model blocks forever (a not-modelled point, an
// empty select; models/README.md).
func try(f func() string) string {
	var res string
	switch o, p := stuck.Run(func() { res = f() }); o {
	case stuck.Stuck:
		if model {
			return "NOT MODELLED"
		}
		return "STUCK"
	case stuck.Panicked:
		return fmt.Sprintf("PANIC %v", p)
	}
	return res
}

func describeHeader(h http.Header) string {
	var hs []string
	for k, vs := range h {
		hs = append(hs, fmt.Sprintf("%s=%q", k, vs))
	}
	sort.Strings(hs)
	return strings.Join(hs, " ")
}

var requestHeads = []string{
	"GET /a?b=c HTTP/1.1\r\nHost: h\r\nX-A: 1\r\nx-a: 2\r\n\r\n",
	"POST /p HTTP/1.0\r\nContent-Length: 3\r\nContent-Type: text/plain\r\n\r\nabcrest",
	"CONNECT /_goRPC_ HTTP/1.0\n\n",
	"CONNECT h:1 HTTP/1.1\r\nHost: h:1\r\n\r\n",
	"PUT http://h/x HTTP/1.1\r\nHost: other\r\nConnection: close\r\nContent-Length: 0\r\n\r\n",
	"GET / HTTP/1.1\r\nHost: h\r\nPragma: no-cache\r\nA:  sp  \r\nB:\t\r\n\r\n",
}

// ReadRequest on request heads and their mutations: the request's fields, header and body, or
// the error.
func TestReadRequest(t *testing.T) {
	var out strings.Builder
	for i, h := range heads(1, requestHeads, 1000) {
		if i > 0 {
			out.WriteString("\n=== ")
		}
		fmt.Fprintf(&out, "%d %q\n", i, h)
		out.WriteString(try(func() string {
			req, err := http.ReadRequest(bufio.NewReader(strings.NewReader(h)))
			if err != nil {
				return fmt.Sprintf("error %T %v", err, err)
			}
			body, berr := io.ReadAll(req.Body)
			return fmt.Sprintf("%s %q %s %d.%d host=%q url=%q close=%v len=%d te=%v\n%s\nbody=%q %v",
				req.Method, req.RequestURI, req.Proto, req.ProtoMajor, req.ProtoMinor, req.Host,
				req.URL.String(), req.Close, req.ContentLength, req.TransferEncoding,
				describeHeader(req.Header), body, berr)
		}))
	}
	golden(t, "readrequest.golden", out.String())
}

var responseHeads = []string{
	"HTTP/1.0 200 Connected to Go RPC\n\n",
	"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nX-A: 1\r\n\r\nokmore",
	"HTTP/1.0 404 Not Found\r\nContent-Type: text/plain\r\n\r\nbody to eof",
	"HTTP/1.1 204 No Content\r\n\r\n",
	"HTTP/1.1 301 Moved\r\nLocation: /x\r\nConnection: close\r\n\r\n",
}

// ReadResponse on response heads and their mutations (the request a CONNECT for the first,
// a GET otherwise).
func TestReadResponse(t *testing.T) {
	var out strings.Builder
	for i, h := range heads(2, responseHeads, 1000) {
		if i > 0 {
			out.WriteString("\n=== ")
		}
		fmt.Fprintf(&out, "%d %q\n", i, h)
		method := "GET"
		if strings.Contains(h, "Connected") {
			method = "CONNECT"
		}
		out.WriteString(try(func() string {
			resp, err := http.ReadResponse(bufio.NewReader(strings.NewReader(h)), &http.Request{Method: method})
			if err != nil {
				return fmt.Sprintf("error %T %v", err, err)
			}
			body, berr := io.ReadAll(resp.Body)
			return fmt.Sprintf("%q %d %s %d.%d close=%v len=%d te=%v uncompressed=%v\n%s\nbody=%q %v",
				resp.Status, resp.StatusCode, resp.Proto, resp.ProtoMajor, resp.ProtoMinor, resp.Close,
				resp.ContentLength, resp.TransferEncoding, resp.Uncompressed, describeHeader(resp.Header),
				body, berr)
		}))
	}
	golden(t, "readresponse.golden", out.String())
}
