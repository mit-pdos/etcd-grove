package echo

import (
	"sync"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/internal/proctest"
)

// The nodes run as separate processes over real TCP (proctest), the programs of
// the distributed adequacy theorem: cmd/server, and the client nodes []string{"junk", "client"}.

// TestProcesses runs the server's process and, against it, each client node's
// process, again and again: every one exits 0 (none panics), and the server is
// still running.
func TestProcesses(t *testing.T) {
	bins := proctest.Build(t, "./cmd/server", "./cmd/client", "./cmd/junk")
	srv := proctest.Start(t, bins["server"])
	proctest.WaitListen(t, SrvAddr)
	for i := 0; i < 10; i++ {
		for _, c := range []string{"junk", "client"} {
			proctest.RunOK(t, bins[c], 20*time.Second)
		}
	}
	srv.Alive(t)
}

// TestServerCrashes kills the server's process (SIGKILL) and restarts it, again
// and again, while client nodes' processes keep running against it: none
// panics, whatever the server's kernel does to their connections (a FIN, a
// reset) and whichever of them a restarted server accepts.
func TestServerCrashes(t *testing.T) {
	bins := proctest.Build(t, "./cmd/server", "./cmd/client", "./cmd/junk")
	srv := proctest.Start(t, bins["server"])
	proctest.WaitListen(t, SrvAddr)
	stop := make(chan struct{})
	var wg sync.WaitGroup
	errs := make(chan error, 64)
	for _, c := range []string{"junk", "client"} {
		wg.Add(1)
		go func(bin string) {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				if err := proctest.Run(bin, 20*time.Second); err != nil {
					errs <- err
					return
				}
			}
		}(bins[c])
	}
	for i := 0; i < 5; i++ {
		time.Sleep(50 * time.Millisecond)
		srv.Kill()
		srv = proctest.Start(t, bins["server"])
		proctest.WaitListen(t, SrvAddr)
	}
	time.Sleep(50 * time.Millisecond)
	close(stop)
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
	srv.Alive(t)
}
