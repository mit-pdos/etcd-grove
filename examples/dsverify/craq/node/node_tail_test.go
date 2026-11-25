package node

import (
	"errors"
	"sync"
	"testing"
	"time"

	"github.com/despreston/go-craq/coordinator"
	"github.com/despreston/go-craq/store/kv"
	"github.com/despreston/go-craq/transport"
)

// fakeNet connects clients to the nodes by address, in process.
type fakeNet struct {
	mu    sync.Mutex
	nodes map[string]*Node
	// hooks run before a client's FwdPropagate and Update (per destination)
	beforeFwd    map[string]func()
	beforeUpdate map[string]func(*transport.NodeMeta) error
}

type netClient struct {
	net *fakeNet
	*Node
	addr string
}

func (c *netClient) Connect(addr string) error {
	c.net.mu.Lock()
	defer c.net.mu.Unlock()
	n, ok := c.net.nodes[addr]
	if !ok {
		return errors.New("no node at " + addr)
	}
	c.Node, c.addr = n, addr
	return nil
}

func (c *netClient) Close() error { return nil }

func (c *netClient) FwdPropagate(r *transport.PropagateRequest) (*transport.PropagateResponse, error) {
	if h := c.net.beforeFwd[c.addr]; h != nil {
		h()
	}
	return c.Node.FwdPropagate(r)
}

func (c *netClient) Update(m *transport.NodeMeta) error {
	if h := c.net.beforeUpdate[c.addr]; h != nil {
		if err := h(m); err != nil {
			return err
		}
	}
	return c.Node.Update(m)
}

type netCoordinator struct {
	*coordinator.Coordinator
}

func (netCoordinator) Connect(string) error { return nil }
func (netCoordinator) Close() error         { return nil }

// newNet is a coordinator and nodes at the addresses (not started).
func newNet(addrs ...string) (*fakeNet, *coordinator.Coordinator, []*Node) {
	fn := &fakeNet{nodes: map[string]*Node{}, beforeFwd: map[string]func(){},
		beforeUpdate: map[string]func(*transport.NodeMeta) error{}}
	tport := func() transport.NodeClient { return &netClient{net: fn} }
	c := coordinator.New(tport)
	var ns []*Node
	for _, a := range addrs {
		n := New(Opts{Address: a, PubAddress: a, CdrAddress: "cdr", Store: kv.New(),
			Transport: tport, CoordinatorClient: netCoordinator{c}})
		fn.nodes[a] = n
		ns = append(ns, n)
	}
	return fn, c, ns
}

func start(t *testing.T, c *coordinator.Coordinator, ns ...*Node) {
	t.Helper()
	for _, n := range ns {
		if err := n.Start(); err != nil {
			t.Fatal(err)
		}
	}
	c.Updates.Wait()
}

// A tail the coordinator removed while it is alive (its ping timed out) must
// not answer reads with its own, now stale, committed version: after a write
// committed by the new tail returned, a read at the removed node returned the
// value before it ("reads return the latest committed version").
func TestReadAtRemovedTail(t *testing.T) {
	_, c, ns := newNet("a", "b")
	start(t, c, ns...)
	if err := c.Write("k", []byte("x")); err != nil {
		t.Fatal(err)
	}
	if err := c.RemoveNode("b"); err != nil {
		t.Fatal(err)
	}
	if err := c.Write("k", []byte("y")); err != nil {
		t.Fatal(err)
	}
	if _, v, err := ns[1].Read("k"); err == nil && string(v) != "y" {
		t.Errorf("read at the removed tail returned %q after the write of y returned", v)
	}
	if _, v, err := ns[0].Read("k"); err != nil || string(v) != "y" {
		t.Errorf("read at the new tail: %q, %v; want y", v, err)
	}
}

// A node that is joining (the tail per the coordinator) must not answer reads
// before it caught up with the chain (J3): a read at it said "key doesn't
// exist" for a key whose write had returned.
func TestReadAtJoiningNode(t *testing.T) {
	fn, c, ns := newNet("a", "b")
	start(t, c, ns[0])
	if err := c.Write("k", []byte("x")); err != nil {
		t.Fatal(err)
	}
	gate := make(chan struct{})
	reached := make(chan struct{})
	fn.beforeFwd["a"] = func() { close(reached); <-gate }
	go ns[1].Start()
	<-reached // b is catching up with a
	res := make(chan string, 1)
	go func() {
		_, v, err := ns[1].Read("k")
		if err != nil {
			res <- "error: " + err.Error()
			return
		}
		res <- string(v)
	}()
	select {
	case r := <-res:
		if r == "error: key doesn't exist" {
			t.Errorf("read at the joining node said the key doesn't exist")
		}
	case <-time.After(100 * time.Millisecond):
	}
	close(gate)
}

// The chain's last node is not removed: it holds the committed versions, and a
// node that joins an empty chain starts empty (a read there said "key doesn't
// exist" after a write had returned).
func TestRemoveLastNode(t *testing.T) {
	_, c, ns := newNet("a", "b")
	start(t, c, ns[0])
	if err := c.Write("k", []byte("x")); err != nil {
		t.Fatal(err)
	}
	c.RemoveNode("a")
	start(t, c, ns[1])
	if _, v, err := ns[1].Read("k"); err == nil && string(v) != "x" || err != nil && err.Error() == "key doesn't exist" {
		t.Errorf("read after the chain's last node was removed: %q, %v; want x", v, err)
	}
}

// After an Update that failed (the node may still apply it later), the
// coordinator sends the node no more metadata: metadata applied out of order
// installs a stale position (a removed tail made the tail again).
func TestNoUpdateAfterFailedUpdate(t *testing.T) {
	fn, c, ns := newNet("a", "b", "c")
	start(t, c, ns...)
	calls := 0
	fn.beforeUpdate["b"] = func(*transport.NodeMeta) error {
		calls++
		return errors.New("timeout")
	}
	c.RemoveNode("c") // b becomes the tail: its Update fails
	c.RemoveNode("a") // b becomes the head
	if calls != 1 {
		t.Errorf("the coordinator sent %d Updates to b after one failed; want none", calls-1)
	}
}
