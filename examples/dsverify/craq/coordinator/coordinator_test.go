package coordinator

import (
	"errors"
	"sync"
	"testing"

	"github.com/despreston/go-craq/transport"
)

// fakeClient is a NodeClient whose Update fails when fail is set.
type fakeClient struct {
	transport.NodeClient
	fail bool
}

func (f *fakeClient) Connect(string) error { return nil }
func (f *fakeClient) Update(*transport.NodeMeta) error {
	if f.fail {
		return errors.New("timeout")
	}
	return nil
}

// updateAll sends the metadata in parallel: a failed Update marks its node
// disconnected while the goroutine updating the next node reads its address.
// Address had a value receiver, which copies the node (connected included): a
// data race (run with -race).
func TestUpdateAllFailedUpdateRace(t *testing.T) {
	for r := 0; r < 50; r++ {
		cdr := New(nil)
		for i, a := range []string{"a", "b", "c", "d"} {
			cdr.replicas = append(cdr.replicas, &node{address: a, connected: true,
				rpc: &fakeClient{fail: i%2 == 0}})
		}
		var wg sync.WaitGroup
		cdr.mu.Lock()
		wg.Add(1)
		go func() { defer wg.Done(); cdr.updateAll(-1) }()
		wg.Wait()
		cdr.mu.Unlock()
	}
}
