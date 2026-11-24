package node

import (
	"sync"
	"testing"
	"time"

	"github.com/despreston/go-craq/coordinator"
	"github.com/despreston/go-craq/store/kv"
	"github.com/despreston/go-craq/transport"
)

// gatedNode is a NodeClient to n whose Write waits for gate to close.
type gatedNode struct {
	FakeNode
	gate chan struct{}
}

func (g *gatedNode) Write(key string, val []byte, version uint64) error {
	<-g.gate
	return g.Node.Write(key, val, version)
}

// Two writes of one key in the chain at once get two versions. The head
// computed the version from its store: with the first write still dirty there
// (its forward not answered yet), store.Read says ErrDirtyItem and the second
// write got version 0 too, so two values had one version (store.Storer:
// ReadVersion "finds an item for the given key with the matching version").
func TestConcurrentWritesDistinctVersions(t *testing.T) {
	gate := make(chan struct{})
	var head, tail *Node
	var c FakeCoordinator
	head = New(Opts{Address: "a", PubAddress: "a", Store: kv.New(), CoordinatorClient: &c,
		Transport: func() transport.NodeClient { return &gatedNode{FakeNode{Node: tail}, gate} }})
	tail = New(Opts{Address: "b", PubAddress: "b", Store: kv.New(), CoordinatorClient: &c,
		Transport: func() transport.NodeClient { return &FakeNode{Node: head} }})
	count := 0
	c = FakeCoordinator{Coordinator: coordinator.New(func() transport.NodeClient {
		defer func() { count++ }()
		if count == 0 {
			return &FakeNode{Node: head}
		}
		return &FakeNode{Node: tail}
	})}
	head.Start()
	tail.Start()
	c.Updates.Wait()

	var wg sync.WaitGroup
	for _, v := range []string{"x", "y"} {
		wg.Add(1)
		go func(v string) { defer wg.Done(); c.Write("hello", []byte(v)) }(v)
	}
	// wait for both writes to be stored at the head (forwards held at the gate)
	for i := 0; i < 200; i++ {
		d, _ := head.store.AllDirty()
		if len(d) == 2 {
			break
		}
		time.Sleep(5 * time.Millisecond)
	}
	d, _ := head.store.AllDirty()
	close(gate)
	wg.Wait()
	if len(d) != 2 {
		t.Fatalf("want two dirty versions at the head, got %d", len(d))
	}
	if d[0].Version == d[1].Version {
		t.Errorf("two writes of one key got the same version %d", d[0].Version)
	}
}
