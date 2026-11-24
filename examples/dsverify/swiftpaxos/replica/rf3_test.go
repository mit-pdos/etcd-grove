package replica

import (
	"testing"
)

// R-F3: a peer's reader adds a late beacon reply's latency to r.Latencies
// under r.M (waitForPeerConnections' GENERIC_SMR_BEACON_REPLY case) at any
// time, also while ComputeClosestPeers computes its result: the latter must
// read r.Latencies under r.M too. Meaningful with -race (a data race).
func TestIssueRF3_LatenciesReadUnderLock(t *testing.T) {
	if !raceOn {
		t.Skip("a data race: run with -race")
	}
	r := newTestReplica(0, []string{"127.0.0.1:1", "127.0.0.1:2", "127.0.0.1:3"})
	// No peer is alive: ComputeClosestPeers sends no beacon.
	stop := make(chan struct{})
	writerDone := make(chan struct{})
	go func() {
		defer close(writerDone)
		for {
			select {
			case <-stop:
				return
			default:
			}
			// What the peer reader does on a beacon reply.
			r.M.Lock()
			r.Latencies[1] = 1
			r.M.Unlock()
		}
	}()
	lat := r.ComputeClosestPeers()
	close(stop)
	<-writerDone
	if len(lat) != 2 {
		t.Fatalf("latencies %v, want 2 entries", lat)
	}
}
