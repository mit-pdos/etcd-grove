// Deterministic test for VerifyLeader counting a non-voter's heartbeat response as a vote (upstream #725).
// verifyLeader sets the verify future's quorum to a majority of the latest configuration's voters, but registers the
// future with every replication goroutine, a non-voter's included, and heartbeat() counts a successful response as
// a vote. A leader cut off from the other voters, with a non-voter still following it in its term, so confirms its
// leadership while the voters have elected a new leader that commits and acknowledges a write. examples/hr3's
// readAt (way 2, as Consul's consistent reads) then reads the old leader's FSM: a stale read.
//
// Only the exported API is used. The test plays the clients itself, with readAt's sequence of raft calls (copied
// below). Each server's transport is inproc's, wrapped only to run a hook just before a TimeoutNow is sent (the test
// uses it to start a network partition at that moment).
//
// Scenario (servers S1..S4; S1..S3 bootstrapped as voters, S4 started empty; pre-vote on; heartbeat, election and
// lease timeouts 1 s):
//  1. K, the first server elected, leads term T'. K adds S4 as a non-voter (AddNonvoter); the configuration
//     {3 voters, S4 non-voter} commits (quorum 2 of the 3 voters).
//  2. Read r0 at K (way 2): K's Barrier of T' is applied (recorded as hr3's readers.barrierIn), the register is
//     empty. Every server holds K's last entry.
//  3. K transfers leadership to j, another voter (LeadershipTransferToServer). Just before K sends TimeoutNow, the
//     network partitions {K, S4} | {j, o} (o the third voter), except the link from K to j, which still delivers
//     the TimeoutNow request (its response is lost; K's transfer fails and K goes on leading term T'). j becomes a
//     candidate, o grants it its vote: j leads term T > T'. The link K -> j is then cut as well.
//  4. A client writes W (Put "w") at j: Apply returns nil, W is committed and acknowledged (j and o).
//  5. Read r1 at K, begun after W was acknowledged: K's term is still T' and its barrier of T' is applied (step 2),
//     so no barrier is issued; VerifyLeader returns nil — its quorum is 2 (of the 3 voters), K's own vote and S4's
//     successful heartbeat response make 2 —; the term is still T'; r1 reads K's FSM, without W.
//
// W completed before r1 began, so r1 must return "w"; the test fails if it returns the empty register. With the
// fix (only voters' heartbeat responses vote), r1's VerifyLeader has K's vote only and never succeeds (K steps down
// when its lease expires): r1 fails its checks, as a read should at a deposed leader.
package verifynonvotervotetest

import (
	"io"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
	"hraftissue/inproc"
)

const n = 4

// nonvoterID: the server added as a non-voter
const nonvoterID = 4

// --- the FSM: a one-key register (hr3's store)

type result struct {
	found bool
	value string
}

type store struct {
	mu      sync.Mutex
	present bool
	value   string
}

func (s *store) Apply(l *raft.Log) interface{} {
	cmd := string(l.Data)
	s.mu.Lock()
	defer s.mu.Unlock()
	if cmd[0] == 'P' {
		s.present = true
		s.value = cmd[1:]
		return result{}
	}
	return result{found: s.present, value: s.value}
}

// read: the store's value now (a read of the FSM's state outside the log)
func (s *store) read() result {
	s.mu.Lock()
	defer s.mu.Unlock()
	return result{found: s.present, value: s.value}
}

func (s *store) Snapshot() (raft.FSMSnapshot, error) { return noSnap{}, nil }
func (s *store) Restore(rc io.ReadCloser) error      { return rc.Close() }

type noSnap struct{}

func (noSnap) Persist(sink raft.SnapshotSink) error { return sink.Close() }
func (noSnap) Release()                             {}

// --- the reads: hr3's readAt, way 2, without the client links (the test is the client)

// readers: the term of each server's last completed Barrier (hr3's readers)
type readers struct {
	mu        sync.Mutex
	barrierIn []uint64
}

// waitFuture: hr3's
func waitFuture(f raft.Future) (error, bool) {
	errCh := make(chan error, 1)
	go func() { errCh <- f.Error() }()
	select {
	case err := <-errCh:
		return err, true
	case <-time.After(time.Second):
		return nil, false
	}
}

// readAt2: hr3's readAt for way 2
func readAt2(rs []*raft.Raft, st []*store, rd *readers, j int) (result, bool) {
	r := rs[j]
	term := r.CurrentTerm()
	rd.mu.Lock()
	have := rd.barrierIn[j] == term
	rd.mu.Unlock()
	if !have {
		if err, ok := waitFuture(r.Barrier(100 * time.Millisecond)); !ok || err != nil {
			return result{}, false
		}
		if r.CurrentTerm() != term {
			return result{}, false
		}
		rd.mu.Lock()
		rd.barrierIn[j] = term
		rd.mu.Unlock()
	}
	if err, ok := waitFuture(r.VerifyLeader()); !ok || err != nil {
		return result{}, false
	}
	if r.CurrentTerm() != term {
		return result{}, false
	}
	return st[j].read(), true
}

// --- the network: inproc's cuts, and a transport that runs a hook before it sends a TimeoutNow

type links struct {
	nw  *inproc.Net
	cut [n + 1][n + 1]bool
}

// set: cut (on) or open the link from a to b (one direction)
func (l *links) set(a, b int, on bool) {
	if l.cut[a][b] != on {
		l.cut[a][b] = on
		l.nw.Cut(a, b, on)
	}
}

func (l *links) openAll() {
	for a := 1; a <= n; a++ {
		for b := 1; b <= n; b++ {
			if a != b {
				l.set(a, b, false)
			}
		}
	}
}

type hookTransport struct {
	*inproc.Transport
	mu           sync.Mutex
	onTimeoutNow func(target int)
}

func (t *hookTransport) setHook(f func(target int)) {
	t.mu.Lock()
	t.onTimeoutNow = f
	t.mu.Unlock()
}

func (t *hookTransport) TimeoutNow(id raft.ServerID, target raft.ServerAddress, args *raft.TimeoutNowRequest,
	resp *raft.TimeoutNowResponse) error {
	t.mu.Lock()
	f := t.onTimeoutNow
	t.mu.Unlock()
	if f != nil {
		for i := 1; i <= n; i++ {
			if inproc.Addr(i) == target {
				f(i)
			}
		}
	}
	return t.Transport.TimeoutNow(id, target, args, resp)
}

func waitFor(t *testing.T, what string, d time.Duration, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(d)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("step did not happen: timed out waiting for %s", what)
		}
		time.Sleep(2 * time.Millisecond)
	}
}

func id(i int) raft.ServerID { return raft.ServerID(inproc.Addr(i)) }

func TestVerifyLeaderNonvoterVote(t *testing.T) {
	nw := inproc.NewNet(n)
	ln := &links{nw: nw}
	var voters []raft.Server
	for i := 1; i <= 3; i++ {
		voters = append(voters, raft.Server{Suffrage: raft.Voter, ID: id(i), Address: inproc.Addr(i)})
	}

	rs := make([]*raft.Raft, n+1)
	st := make([]*store, n+1)
	tr := make([]*hookTransport, n+1)
	rd := &readers{barrierIn: make([]uint64, n+1)}
	for i := 1; i <= n; i++ {
		conf := raft.DefaultConfig()
		conf.LocalID = id(i)
		conf.HeartbeatTimeout = time.Second
		conf.ElectionTimeout = time.Second
		conf.LeaderLeaseTimeout = time.Second
		conf.CommitTimeout = 5 * time.Millisecond
		conf.SnapshotThreshold = 1 << 62
		conf.SnapshotInterval = time.Hour
		logs := raft.NewInmemStore()
		stable := raft.NewInmemStore()
		snaps := raft.NewInmemSnapshotStore()
		tr[i] = &hookTransport{Transport: nw.Transport(i)}
		if i != nonvoterID {
			if err := raft.BootstrapCluster(conf, logs, stable, snaps, tr[i], raft.Configuration{Servers: voters}); err != nil {
				t.Fatal(err)
			}
		}
		st[i] = &store{}
		r, err := raft.NewRaft(conf, st[i], logs, stable, snaps, tr[i])
		if err != nil {
			t.Fatal(err)
		}
		rs[i] = r
	}
	t.Cleanup(func() {
		ln.openAll()
		done := make(chan struct{})
		go func() {
			for i := 1; i <= n; i++ {
				rs[i].Shutdown().Error()
			}
			close(done)
		}()
		select {
		case <-done:
		case <-time.After(10 * time.Second):
			t.Log("shutdown timed out")
		}
	})

	// 1. K: the first leader; it adds S4 as a non-voter
	var k int
	waitFor(t, "a leader", 10*time.Second, func() bool {
		for i := 1; i <= 3; i++ {
			if rs[i].State() == raft.Leader {
				k = i
				return true
			}
		}
		return false
	})
	termK := rs[k].CurrentTerm()
	if err, ok := waitFuture(rs[k].AddNonvoter(id(nonvoterID), inproc.Addr(nonvoterID), 0, 0)); !ok || err != nil {
		t.Fatalf("step did not happen: K's AddNonvoter(S4): %v (answered %v)", err, ok)
	}

	// 2. r0 at K: K's barrier of T' applied; every server holds K's last entry
	if res, ok := readAt2(rs, st, rd, k); !ok || res.found {
		t.Fatalf("step did not happen: r0 at K (S%d): %+v ok=%v, want the empty register", k, res, ok)
	}
	if got := rs[k].CurrentTerm(); got != termK {
		t.Fatalf("step did not happen: K's term moved from %d to %d", termK, got)
	}
	last := rs[k].LastIndex()
	waitFor(t, "every server to hold K's last entry", 5*time.Second, func() bool {
		for i := 1; i <= n; i++ {
			if rs[i].LastIndex() < last {
				return false
			}
		}
		return true
	})
	cfg := rs[k].GetConfiguration()
	if err := cfg.Error(); err != nil {
		t.Fatal(err)
	}
	for _, s := range cfg.Configuration().Servers {
		want := raft.Voter
		if s.ID == id(nonvoterID) {
			want = raft.Nonvoter
		}
		if s.Suffrage != want {
			t.Fatalf("step did not happen: K's configuration %+v", cfg.Configuration())
		}
	}

	// 3. K transfers leadership to j; the partition {K, S4} | {j, o} starts just before the TimeoutNow is sent,
	// whose request still reaches j
	j, o := 0, 0
	for i := 1; i <= 3; i++ {
		if i != k {
			if j == 0 {
				j = i
			} else {
				o = i
			}
		}
	}
	nv := nonvoterID
	tr[k].setHook(func(target int) {
		if target != j {
			return
		}
		ln.set(j, k, true)
		ln.set(o, k, true)
		ln.set(k, o, true)
		ln.set(j, nv, true)
		ln.set(nv, j, true)
		ln.set(o, nv, true)
		ln.set(nv, o, true)
	})
	err, ok := waitFuture(rs[k].LeadershipTransferToServer(id(j), inproc.Addr(j)))
	t.Logf("K's leadership transfer to j: %v (answered %v)", err, ok)
	tr[k].setHook(nil)
	waitFor(t, "j to lead a later term", 5*time.Second, func() bool {
		return rs[j].State() == raft.Leader && rs[j].CurrentTerm() > termK
	})
	termJ := rs[j].CurrentTerm()
	ln.set(k, j, true)

	// 4. W at j: committed and acknowledged
	if err, ok := waitFuture(rs[j].Apply([]byte("Pw"), 0)); !ok || err != nil {
		t.Fatalf("step did not happen: W at j (S%d): %v (answered %v)", j, err, ok)
	}
	t.Logf("W acknowledged by j (S%d, term %d)", j, termJ)

	// 5. r1 at K, begun after W was acknowledged
	if rs[k].State() != raft.Leader || rs[k].CurrentTerm() != termK {
		t.Fatalf("step did not happen: K (S%d) is %v in term %d, want leader in term %d", k, rs[k].State(),
			rs[k].CurrentTerm(), termK)
	}
	r1, ok := readAt2(rs, st, rd, k)
	if !ok {
		t.Logf("r1 at K (S%d) failed its checks (K now %v in term %d): no stale read", k, rs[k].State(),
			rs[k].CurrentTerm())
		return
	}
	if !r1.found || r1.value != "w" {
		t.Errorf("not linearizable (stale read): W (Put \"w\") was acknowledged by the leader j (S%d, term %d, "+
			"voters j and S%d); r1 at K (S%d), begun after that, passed every check of readAt (barrier of term %d "+
			"applied, VerifyLeader nil, term unchanged) and returned %+v; K's VerifyLeader was confirmed by its own "+
			"vote and the non-voter S%d's heartbeat response", j, termJ, o, k, termK, r1, nv)
	} else {
		t.Logf("r1 at K returned %q", r1.value)
	}
}
