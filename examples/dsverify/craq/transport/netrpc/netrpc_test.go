//go:build !netmodel

// (A test of the real net/rpc only: in a model build net/rpc needs the program's codec, which
// the kit registers, examples/craqnet.)

package netrpc

import (
	"errors"
	"net"
	"net/http"
	"net/rpc"
	"testing"

	"github.com/despreston/go-craq/transport"
)

// fakeNode is a NodeService whose LatestVersion answers (key, 7) and whose
// propagation methods fail.
type fakeNode struct{ transport.NodeService }

func (fakeNode) LatestVersion(key string) (string, uint64, error) { return key, 7, nil }

var errStore = errors.New("store failed")

func (fakeNode) FwdPropagate(*transport.PropagateRequest) (*transport.PropagateResponse, error) {
	return nil, errStore
}

func (fakeNode) BackPropagate(*transport.PropagateRequest) (*transport.PropagateResponse, error) {
	return nil, errStore
}

// NodeClient.LatestVersion calls the node's LatestVersion (N1: it called
// "RPC.Commit" with a string argument, which the server rejects, so every read
// of a dirty key at a node other than the tail failed).
func TestNodeClientLatestVersion(t *testing.T) {
	srv := rpc.NewServer()
	if err := srv.RegisterName("RPC", &NodeBinding{Svc: fakeNode{}}); err != nil {
		t.Fatal(err)
	}
	mux := http.NewServeMux()
	mux.Handle(rpc.DefaultRPCPath, srv)
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go http.Serve(l, mux)

	nc := NewNodeClient()
	if err := nc.Connect(l.Addr().String()); err != nil {
		t.Fatal(err)
	}
	defer nc.Close()
	k, v, err := nc.LatestVersion("hello")
	if err != nil || k != "hello" || v != 7 {
		t.Errorf("LatestVersion(hello) = %q, %d, %v; want hello, 7, nil", k, v, err)
	}
}

// The bindings return the service's propagation error (N2: they dereferenced
// the nil response before looking at the error).
func TestNodeBindingPropagateError(t *testing.T) {
	nb := &NodeBinding{Svc: fakeNode{}}
	req := transport.PropagateRequest{}
	var rep transport.PropagateResponse
	if err := nb.FwdPropagate(&req, &rep); err != errStore {
		t.Errorf("FwdPropagate: want the store's error, got %v", err)
	}
	if err := nb.BackPropagate(&req, &rep); err != errStore {
		t.Errorf("BackPropagate: want the store's error, got %v", err)
	}
}
