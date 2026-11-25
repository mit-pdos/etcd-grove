package kvraft

import (
	"testing"
	"time"
)

// TestRestartInProcess restarts a replica in its process (Node.restart: Replica.stop, raft's
// Node.Stop, then the next incarnation from the file) again and again, a write acknowledged
// between two restarts each time, and checks that every new incarnation serves requests and that
// every acknowledged write survives every later restart: the path of ReqDisrupt's restart runs,
// and the incarnation it starts works.
func TestRestartInProcess(t *testing.T) {
	cfg := NodeConfig{ID: 1, Dir: t.TempDir(), Addrs: map[uint64]string{1: "127.0.0.1:1"},
		Opts: Options{Voters: 1, MaxSizePerMsg: 4 << 10, MaxCommittedSizePerReady: 4 << 10, MaxInflightMsgs: 4}}
	n := StartNode(cfg)
	const rounds = 20
	for i := uint64(0); i < rounds; i++ {
		key := "k" + itoa(i)
		// a client's retries of the same operation (applied once): a write waits for its entry's
		// fsync, which a busy disk can make slow
		put := false
		for try := 0; try < 15 && !put; try++ {
			_, put = n.handle(ReqPropose, EncodeOp(100+i, OpPut, key, "v"+itoa(i)), 2*time.Second)
		}
		if !put {
			t.Fatalf("round %d: Put not answered", i)
		}
		if _, ok := n.handle(ReqDisrupt, EncodeDisrupt(3, 0), time.Second); !ok {
			t.Fatalf("round %d: restart not answered", i)
		}
		for j := uint64(0); j <= i; j++ {
			// a client's retries: a read reaching an incarnation that knows no leader yet is dropped
			var v []byte
			ok := false
			for try := uint64(0); try < 60 && !ok; try++ {
				v, ok = n.handle(ReqRead, EncodeRead(100000*(i+1)+100*j+try, "k"+itoa(j)), time.Second)
			}
			if !ok || string(v) != "v"+itoa(j) {
				t.Fatalf("round %d: Read k%d after restart = %q, %v", i, j, v, ok)
			}
		}
	}
	s := n.stats.Snapshot()
	if s[StRestartsInProcess] != rounds {
		t.Fatalf("restarts in process %d, want %d", s[StRestartsInProcess], rounds)
	}
	r := n.current()
	r.stop()
	t.Logf("%s", FormatStats(s))
}
