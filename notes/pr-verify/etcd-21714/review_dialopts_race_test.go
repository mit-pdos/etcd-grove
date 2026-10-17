package clientv3

import (
	"sync"
	"testing"

	"google.golang.org/grpc"
)

// New's spec (and dialWithBalancer's postulate) requires nothing of cfg.DialOptions' elements,
// so a caller that owns the slice may write it while New runs; dial() reads it
// (append(opts, c.cfg.DialOptions...)). Run with -race.
func TestReviewNewDialOptionsRace(t *testing.T) {
	opts := []grpc.DialOption{grpc.WithUserAgent("a")}
	var wg sync.WaitGroup
	wg.Add(1)
	stop := make(chan struct{})
	go func() {
		defer wg.Done()
		for {
			select {
			case <-stop:
				return
			default:
				opts[0] = grpc.WithUserAgent("b")
			}
		}
	}()
	for i := 0; i < 20; i++ {
		c, err := New(Config{Endpoints: []string{"127.0.0.1:1"}, DialOptions: opts})
		if err == nil {
			c.Close()
		}
	}
	close(stop)
	wg.Wait()
}
