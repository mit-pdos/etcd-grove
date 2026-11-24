// Package httpreserve: a counterexample to http.reserve's spec before 2026-11-24 (with RoundTrip's,
// roundTripperOk; notes/axiom-review/http-reserve-addrproto.md), after http.register's netAddrLeft fix
// (examples/axiomcx/httpaddrleft).
//
// The program reserves Addr's HTTP protocol P (reserve, from startRights' httpProtoFree Addr), whose
// resp admits only the server's own statuses and 204 (P.srvOk holds). It never registers Addr:
// net.Listen(Addr) gives netListenerAt l Addr and netAddrLeft Addr, and the program serves Addr with
// raw net code (Listener.Accept, Conn.Write over the net extension, after addr_set_proto_tok sets
// Addr's net protocols to trivial ones, or with netPend Addr ∅ kept so that Accept's Qok is
// vacuous). RoundTrip's post (`□ ∃ w, P.resp R γk st w`) then says st ≠ 200, while the raw server
// answers 200. Main panics. Fixed by reserve taking Addr's net protocols as net/http's (httpAddrNet,
// set from netAddrFree Addr): the program then has no netAddrFree Addr to listen raw with, no
// netAddrLeft Addr, and a raw acceptor at Addr can write nothing (httpNetSrvP is opaque).
package httpreserve

import (
	"context"
	"net"
	"net/http"

	"go.etcd.io/etcd/client/pkg/v3/transport"
)

const Addr = "127.0.0.1:23931"

// rawServe: the raw server (verified over the net extension): answers every connection with 200.
func rawServe(l net.Listener) {
	for {
		c, err := l.Accept()
		if err != nil {
			return
		}
		buf := make([]byte, 4096)
		c.Read(buf)
		c.Write([]byte("HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"))
		c.Close()
	}
}

func Main() {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	go rawServe(l)
	tr, err := transport.NewTimeoutTransport(transport.TLSInfo{}, 0, 0, 0)
	if err != nil {
		return
	}
	req, err := http.NewRequest("GET", "http://"+Addr+"/", nil)
	if err != nil {
		return
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	req = req.WithContext(ctx)
	resp, err := tr.RoundTrip(req)
	if err != nil {
		return
	}
	// RoundTrip's post: □ ∃ w, P.resp R γk st w, P.resp R γk st w := st ∈ srvStatuses ∨ st = 204.
	if resp.StatusCode == 200 {
		panic("httpreserve: RoundTrip returned a status the reserved protocol excludes")
	}
}
