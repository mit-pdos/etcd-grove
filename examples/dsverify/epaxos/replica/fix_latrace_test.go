package replica

import (
	"bufio"
	"bytes"
	"io"
	"net"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
)

// TestComputeClosestPeersLateBeaconReply: replica 0 of 2, connected to peer 1 (in memory),
// runs ComputeClosestPeers; peer 1 answers a beacon only after ComputeClosestPeers has
// returned (a late BEACON_REPLY: time is not modeled). replicaListener writes r.Latencies[1]
// under r.M; ComputeClosestPeers' final read of it must be under r.M too: under -race, no data
// race may be reported.
func TestComputeClosestPeersLateBeaconReply(t *testing.T) {
	r := New("n0", 0, 0, []string{"127.0.0.1:1", "127.0.0.1:2"}, false, true, false,
		&config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
	mine, theirs := net.Pipe()
	defer theirs.Close()
	r.M.Lock()
	r.Peers[1] = mine
	r.PeerReaders[1] = bufio.NewReader(mine)
	r.PeerWriters[1] = bufio.NewWriter(mine)
	r.Alive[1] = true
	r.M.Unlock()
	go r.replicaListener(1, r.PeerReaders[1])

	// Peer 1 reads the 20 beacons and answers the last one 1 s after it: ComputeClosestPeers
	// computes its quorum 0.5 s after its last beacon, then reads r.Latencies. The reply is
	// written by this goroutine, which does not synchronize with ComputeClosestPeers' goroutine
	// (the race detector reports unordered accesses whichever happens first).
	go func() {
		var b [9]byte
		for n := 0; n < 20; n++ {
			if _, err := io.ReadFull(theirs, b[:]); err != nil {
				return
			}
		}
		var bc defs.Beacon
		bc.Unmarshal(bytes.NewReader(b[1:]))
		time.Sleep(time.Second)
		w := bufio.NewWriter(theirs)
		w.WriteByte(defs.GENERIC_SMR_BEACON_REPLY)
		(&defs.BeaconReply{Timestamp: bc.Timestamp}).Marshal(w)
		w.Flush()
	}()

	// recorded: the reply's write, seen by a goroutine that does not synchronize with
	// ComputeClosestPeers' goroutine either (the test goroutine does, through done).
	recorded := make(chan bool)
	go func() {
		for i := 0; i < 3000; i++ {
			r.M.Lock()
			l := r.Latencies[1]
			r.M.Unlock()
			if l != 0 {
				recorded <- true
				return
			}
			time.Sleep(10 * time.Millisecond)
		}
		recorded <- false
	}()

	done := make(chan bool)
	go func() {
		r.ComputeClosestPeers()
		done <- true
	}()
	if !<-recorded {
		t.Fatal("the beacon reply was not recorded")
	}
	<-done
}
