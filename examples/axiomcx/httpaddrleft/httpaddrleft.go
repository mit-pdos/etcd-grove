// Package httpaddrleft: a counterexample to http.register's spec before 2026-11-24
// (notes/axiom-review/http-register-addrleft.md). net.Listen's netAddrLeft sets the address's net
// protocols (to trivial ones, addr_set_proto_tok), while http.register took only the listener
// (netListenerAt), so a raw net client of the same program writes a request the HTTP protocol
// excludes, and http.Serve_ok's handler contract (`□ (H.proto a).req R`) promises the handler it
// cannot happen. Main panics (in the handler's goroutine).
package httpaddrleft

import (
	"net"
	"net/http"
	"time"
)

const Addr = "127.0.0.1:23901"

type handler struct{}

// ServeHTTP: the protocol at Addr says every request is a POST (P.req R := R.meth = "POST").
func (handler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	m := r.Method
	go func() {
		if m != "POST" {
			panic("httpaddrleft: the handler got a request its address's protocol excludes")
		}
	}()
}

func holdForever() {
	for {
		time.Sleep(time.Hour)
	}
}

func Main() {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	go http.Serve(l, handler{})
	c, err := net.Dial("tcp", Addr)
	if err != nil {
		return
	}
	c.Write([]byte("GET / HTTP/1.1\r\nHost: 127.0.0.1:23901\r\n\r\n"))
	holdForever()
}
