package clientv3

import (
	"sync"
	"testing"
)

// Client.Dial (exported) reads c.endpoints[0] in dial() without c.epMu, while SetEndpoints
// (exported; also autoSync's Sync) writes c.endpoints under c.epMu. Run with -race.
func TestReviewDialSetEndpointsRace(t *testing.T) {
	c, err := New(Config{Endpoints: []string{"127.0.0.1:1"}})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := 0; i < 100; i++ {
			c.SetEndpoints("127.0.0.1:2", "127.0.0.1:3")
		}
	}()
	for i := 0; i < 100; i++ {
		if cc, err := c.Dial("127.0.0.1:4"); err == nil {
			cc.Close()
		}
	}
	wg.Wait()
}
