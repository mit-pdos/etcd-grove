package client

import (
	"net"
	"sync"
	"time"
)

// How many times, and how far apart, AwaitAccept tries to connect to an address.
const (
	acceptTries = 300
	acceptPause = 100 * time.Millisecond
)

// AwaitAccept waits until every address accepts a TCP connection (a liveness wait: a connection
// that carries no request runs nothing), trying each for 30 seconds, and reports whether all did.
func AwaitAccept(addrs []string) bool {
	for _, a := range addrs {
		up := false
		for t := 0; t < acceptTries && !up; t++ {
			c, err := net.DialTimeout("tcp", a, time.Second)
			if err == nil {
				c.Close()
				up = true
			} else {
				time.Sleep(acceptPause)
			}
		}
		if !up {
			return false
		}
	}
	return true
}

// Rotate is xs from its i-th (mod len) element on: the clients of a workload made of the same
// endpoints prefer different members (a client's balancer picks among the endpoints, the first
// first).
func Rotate[T any](xs []T, i int) []T {
	k := len(xs)
	out := make([]T, k)
	for j := 0; j < k; j++ {
		x := xs[(i+j)%k]
		out[j] = x
	}
	return out
}

// CallAll runs call at every address addrs[c] with the input ins[c], all at once, and returns
// their outputs and whether each answered.
func CallAll[I, O any](addrs []string, ins []I, call func(addr string, in I) (O, bool)) ([]O, []bool) {
	outs := make([]O, len(addrs))
	oks := make([]bool, len(addrs))
	var wg sync.WaitGroup
	for c := range addrs {
		wg.Add(1)
		go func() {
			outs[c], oks[c] = call(addrs[c], ins[c])
			wg.Done()
		}()
	}
	wg.Wait()
	return outs, oks
}
