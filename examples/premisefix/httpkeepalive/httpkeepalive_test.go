// Package httpkeepalive records, for the restart boundary's future review, what closing a served
// listener does not stop (Proof/net/http/ListenerClose.lean, header; http-boundary-fix, second
// review, 2026-11-14): after l.Close() and http.Serve's return, a client's idle keep-alive
// connection to the old Serve still starts new runs of the OLD handler, also after a new listener
// at the same address serves a new handler. The test passes when it observes that.
package httpkeepalive

import (
	"io"
	"net"
	"net/http"
	"testing"
)

func TestOldServeKeepsConns(t *testing.T) {
	l1, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := l1.Addr().String()
	done := make(chan struct{})
	go func() {
		http.Serve(l1, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, "old") }))
		close(done)
	}()
	c := &http.Client{Transport: &http.Transport{}}
	get := func() string {
		resp, err := c.Post("http://"+addr+"/raft", "x", nil)
		if err != nil {
			return "err: " + err.Error()
		}
		b, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return string(b)
	}
	if got := get(); got != "old" {
		t.Fatalf("before close: %q", got)
	}
	l1.Close()
	<-done
	l2, err := net.Listen("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	defer l2.Close()
	go http.Serve(l2, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, "new") }))
	if got := get(); got != "old" {
		t.Errorf("after the re-listen: %q; want the old Serve's handler, on the kept connection", got)
	}
}
