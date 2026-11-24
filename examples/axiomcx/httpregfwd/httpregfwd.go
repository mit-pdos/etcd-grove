// Package httpregfwd: a counterexample to http.register's spec before 2026-11-24's netListenerOpen fix
// (notes/axiom-review/http-reserve-addrproto.md, "the listener's tie"). netListenerOpen l a said only
// that l is some *TCPListener t and that some extension listener lv is open at a, nothing tying t to
// lv (Net's isListener does: lisAt t lv x, t ↦□ TCPListener{lid: lv, ...}). So the facts of the
// listener at the reserved address A (net.Listen.specHttp) repack around the Go value of a raw
// listener at an unreserved B, http.register(lb, A, P) and Serve_ok promise the handler P.req of
// every request (P.req R := R.meth = "GET"), while the program's raw client writes a POST to B
// (whose net protocols it set to trivial ones). Main panics (in the handler's goroutine).
package httpregfwd

import (
	"net"
	"net/http"
	"time"
)

// A is reserved for HTTP (program start's As; listened with net.Listen.specHttp); B is not (the
// program sets its net protocols to trivial ones and serves it raw).
const (
	A = "127.0.0.1:23811"
	B = "127.0.0.1:23812"
)

func Main() {
	la, err := net.Listen("tcp", A) // specHttp: netListenerAt la A
	if err != nil {
		return
	}
	_ = la                          // never served: its netLis/netLisAt went into a forged netListenerOpen lb A
	lb, err := net.Listen("tcp", B) // Net's Listen.spec_addrOk with listen_au (B's addrProto)
	if err != nil {
		return
	}
	// register(lb, A, P): P.req R := R.meth = "GET"
	go http.Serve(lb, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != "GET" { // dead by Serve_ok: □ P.req R and reqAt's Method
			go func() { panic("httpregfwd: the handler got a request its address's protocol excludes") }()
		}
	}))
	c, err := net.Dial("tcp", B) // dial_au at B (trivial protocols)
	if err != nil {
		return
	}
	c.Write([]byte("POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\n\r\n")) // writeP, □ True
	for {
		time.Sleep(time.Second)
	}
}
