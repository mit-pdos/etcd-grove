package node

import (
	"errors"
	"fmt"
	"sync"
	"testing"

	"github.com/despreston/go-craq/store/kv"
	"github.com/despreston/go-craq/transport"
)

// newTail is the tail of a started two-node chain.
func newTail(t *testing.T) *Node {
	t.Helper()
	n, n2, c := setupTwoNodeChain()
	if err := n.Start(); err != nil {
		t.Fatal(err)
	}
	if err := n2.Start(); err != nil {
		t.Fatal(err)
	}
	c.Updates.Wait()
	if !n2.IsTail || n.IsTail {
		t.Fatal("the second node is not the tail")
	}
	return n2
}

// Concurrent writes at the tail, each in its own request (net/rpc runs every
// request in a goroutine of its own), commit concurrently: n.latest was written
// without the lock (C1: "fatal error: concurrent map writes").
func TestConcurrentWritesAtTail(t *testing.T) {
	n := newTail(t)
	var wg sync.WaitGroup
	for i := 0; i < 200; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			n.Write(fmt.Sprintf("k%d", i), []byte("v"), 1)
		}(i)
	}
	wg.Wait()
	for i := 0; i < 200; i++ {
		if _, v, _ := n.LatestVersion(fmt.Sprintf("k%d", i)); v != 1 {
			t.Fatalf("LatestVersion(k%d) = %d, want 1", i, v)
		}
	}
}

// Commits arrive in any order: the node's latest version of a key is the newest
// committed one ("latest: Latest version of a given key"), not the last commit.
func TestLatestVersionKeepsNewest(t *testing.T) {
	n := newTail(t)
	n.Write("hello", []byte("two"), 2)
	n.Write("hello", []byte("one"), 1)
	if _, v, _ := n.LatestVersion("hello"); v != 2 {
		t.Errorf("LatestVersion(hello) = %d after committing 2 then 1; want 2", v)
	}
}

// A node that is not the tail and has no successor fails the write (R4: it
// dereferenced the missing successor).
func TestWriteWithoutSuccessor(t *testing.T) {
	n := New(Opts{Store: kv.New(), Transport: func() transport.NodeClient { return &FakeNode{} }})
	if err := n.Write("hello", []byte("world"), 1); err == nil {
		t.Errorf("Write at a node with no successor that is not the tail succeeded")
	}
}

type failingCoordinator struct {
	transport.CoordinatorClient
}

func (failingCoordinator) Connect(string) error { return errors.New("unreachable") }

// A node whose announcement to the coordinator fails reports the error (F1: it
// called log.Fatalf, which exits the node's process).
func TestStartJoinFails(t *testing.T) {
	n := New(Opts{
		Store:             kv.New(),
		CdrAddress:        "coordinator",
		CoordinatorClient: failingCoordinator{},
		Transport:         func() transport.NodeClient { return &FakeNode{} },
	})
	if err := n.Start(); err == nil {
		t.Errorf("Start succeeded although the coordinator is unreachable")
	}
}
