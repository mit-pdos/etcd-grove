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

	"github.com/despreston/go-craq/coordinator"
	"github.com/despreston/go-craq/node"
	"github.com/despreston/go-craq/store/kv"
	"github.com/despreston/go-craq/transport"
)

// silentFail is a node client whose calls fail with an error whose message is
// empty.
type silentFail struct{ transport.NodeClient }

func (silentFail) Connect(string) error { return nil }
func (silentFail) Close() error          { return nil }
func (silentFail) Write(string, []byte, uint64) error {
	return errors.New("")
}
func (silentFail) Update(*transport.NodeMeta) error { return nil }
func (silentFail) BackPropagate(*transport.PropagateRequest) (*transport.PropagateResponse, error) {
	return &transport.PropagateResponse{}, nil
}

func serve(t *testing.T, rcvr interface{}) string {
	t.Helper()
	srv := rpc.NewServer()
	if err := srv.RegisterName("RPC", rcvr); err != nil {
		t.Fatal(err)
	}
	mux := http.NewServeMux()
	mux.Handle(rpc.DefaultRPCPath, srv)
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	go http.Serve(l, mux)
	return l.Addr().String()
}

// net/rpc sends a method's error as its message, and an empty message means
// success: a method must not return an error whose message may be empty. The
// node returned its successor's error, and the coordinator the head's, as they
// were: a failed forward whose error had an empty message was a successful
// write for the caller.
func TestFailedWriteIsAnError(t *testing.T) {
	// A node (not the tail) whose successor fails silently.
	n := node.New(node.Opts{Store: kv.New(), Transport: func() transport.NodeClient { return silentFail{} }})
	if err := n.Update(&transport.NodeMeta{IsHead: true, Next: "succ", Tail: "succ"}); err != nil {
		t.Fatal(err)
	}
	nc := NewNodeClient()
	if err := nc.Connect(serve(t, &NodeBinding{Svc: n})); err != nil {
		t.Fatal(err)
	}
	if err := nc.Write("k", []byte("v"), 1); err == nil {
		t.Errorf("node Write succeeded although the forward to the successor failed")
	}

	// A coordinator whose head fails silently.
	c := coordinator.New(func() transport.NodeClient { return silentFail{} })
	if _, err := c.AddNode("head"); err != nil {
		t.Fatal(err)
	}
	cc := NewCoordinatorClient()
	if err := cc.Connect(serve(t, &CoordinatorBinding{Svc: c})); err != nil {
		t.Fatal(err)
	}
	if err := cc.Write("k", []byte("v")); err == nil {
		t.Errorf("coordinator Write succeeded although the head's write failed")
	}
}

// silentDial is a node client whose Connect fails with an empty message.
type silentDial struct{ transport.NodeClient }

func (silentDial) Connect(string) error { return errors.New("") }

// The same for Update: a node whose connection to its new predecessor failed
// (with an empty message) reported a successful Update.
func TestFailedUpdateIsAnError(t *testing.T) {
	n := node.New(node.Opts{Store: kv.New(), Transport: func() transport.NodeClient { return silentDial{} }})
	nc := NewNodeClient()
	if err := nc.Connect(serve(t, &NodeBinding{Svc: n})); err != nil {
		t.Fatal(err)
	}
	if err := nc.Update(&transport.NodeMeta{Prev: "pred", Tail: "pred"}); err == nil {
		t.Errorf("Update succeeded although connecting to the predecessor failed")
	}
}

// silentCommit is a node client whose Commit fails with an empty message.
type silentCommit struct{ transport.NodeClient }

func (silentCommit) Connect(string) error { return nil }
func (silentCommit) Close() error          { return nil }
func (silentCommit) Commit(string, uint64) error {
	return errors.New("")
}
func (silentCommit) FwdPropagate(*transport.PropagateRequest) (*transport.PropagateResponse, error) {
	return &transport.PropagateResponse{}, nil
}

// Commit and AddNode, too: a node whose forward of a commit to its predecessor
// failed, and a coordinator that could not reach the new node, returned the
// cause's error as it was (empty message: success for the caller).
func TestFailedCommitAndAddNodeAreErrors(t *testing.T) {
	n := node.New(node.Opts{Store: kv.New(), Transport: func() transport.NodeClient { return silentCommit{} }})
	if err := n.Update(&transport.NodeMeta{Prev: "pred", Tail: "tail"}); err != nil {
		t.Fatal(err)
	}
	n.Write("k", []byte("v"), 1) // stored dirty (no successor: fails)
	nc := NewNodeClient()
	if err := nc.Connect(serve(t, &NodeBinding{Svc: n})); err != nil {
		t.Fatal(err)
	}
	if err := nc.Commit("k", 1); err == nil {
		t.Errorf("Commit succeeded although forwarding it to the predecessor failed")
	}

	c := coordinator.New(func() transport.NodeClient { return silentDial{} })
	cc := NewCoordinatorClient()
	if err := cc.Connect(serve(t, &CoordinatorBinding{Svc: c})); err != nil {
		t.Fatal(err)
	}
	if _, err := cc.AddNode("new"); err == nil {
		t.Errorf("AddNode succeeded although the coordinator could not connect to the node")
	}
}
