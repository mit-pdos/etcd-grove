// Deterministic test for reads with VerifyLeader at a leader that is its configuration's only voter. A variant of
// verify/issues/verify-read-fsm-lag: there, VerifyLeader responded as soon as a quorum answered, without waiting for
// the leader's FSM to reach its commit index (Raft's read-only queries, Ongaro's dissertation 6.4, step 4), and the fix
// (leaderLoop) sends the verified future through fsmMutateCh. verifyLeader's hot path for a quorum of one (the leader
// is the only voter of its latest configuration) still responds at once, without that wait. With membership changes
// a configuration of one voter is reachable, and a non-voter applies the leader's committed entries from its commit
// index, possibly before the leader's own FSM does.
//
// Only the exported API is used: BootstrapCluster, DemoteVoter, Apply, Barrier, VerifyLeader, CurrentTerm, State,
// GetConfiguration, over examples/inproc with no partition and no lost message. The test plays the clients itself,
// with examples/hr3's readAt (way 2) sequence of raft calls (copied below, with a pause point between the final term
// check and the FSM read). The FSM is a one-key register (hr3's store) whose Apply of a given command blocks at a given
// server until the test releases it (an FSM that is slow to apply).
//
// Scenario (3 voters S1..S3, pre-vote on):
//  1. j, the first server elected, leads term T_j. The register is empty.
//  2. Read r1 at j (way 2): j's Barrier of T_j is applied, VerifyLeader returns nil (a quorum of the three voters),
//     the term is still T_j. r1 pauses just before it reads j's FSM.
//  3. At j: DemoteVoter of X (the third server), then DemoteVoter of j itself. Once the second commits, j steps down
//     (it has no vote in its committed configuration) and the configuration is {K voter, j and X non-voters}.
//  4. K, the only voter, is elected in term T > T_j. j follows K as a non-voter (K replicates to it).
//  5. Read r0 at K (way 2) issues K's Barrier of T (so K's FSM has applied a barrier of its term) and returns the
//     empty register.
//  6. K's FSM is set to block its Apply of W (Put "w"). A client sends W to K (its outcome stays unknown to the
//     test). K commits W alone (quorum one); j learns K's commit index and applies W.
//  7. r1 goes on: it reads j's FSM, sees "w", and returns.
//  8. Read r2 at K (way 2), begun after r1 returned: K's barrier of T is applied (step 5), VerifyLeader returns nil
//     (hot path: K's own vote is a quorum), the term is still T; r2 reads K's FSM, which has not applied W yet.
//
// r1 returned W's value and r2 began after r1 returned, so r2 must return it too (no other write exists); the test
// fails if r2 misses it. A goroutine releases K's FSM 300 ms after r2 began: with the fix (the hot path also responds
// from the FSM goroutine, after the batches committed before it), r2's VerifyLeader waits for it and r2 sees "w".
package verifysinglevoterfsmlagtest

import (
	"io"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
	"hraftissue/inproc"
)

const n = 3

// --- the FSM: a one-key register (hr3's store); Apply of the command blockCmd waits on release first, before it
// takes the mutex (the FSM goroutine is slow to apply it; the state stays readable)

type result struct {
	found bool
	value string
}

type store struct {
	mu      sync.Mutex
	present bool
	value   string

	bmu      sync.Mutex
	blockCmd string        // "" : none
	blocked  chan struct{} // closed when Apply of blockCmd waits
	release  chan struct{} // closed by the test
	applied  chan struct{} // closed when Apply of watchCmd has updated the state
	watchCmd string
	watched  bool
}

func newStore() *store {
	return &store{blocked: make(chan struct{}), release: make(chan struct{}), applied: make(chan struct{})}
}

func (s *store) Apply(l *raft.Log) interface{} {
	cmd := string(l.Data)
	s.bmu.Lock()
	block := s.blockCmd != "" && cmd == s.blockCmd
	if block {
		s.blockCmd = ""
	}
	s.bmu.Unlock()
	if block {
		close(s.blocked)
		<-s.release
	}
	s.mu.Lock()
	var res interface{}
	if cmd[0] == 'P' {
		s.present = true
		s.value = cmd[1:]
		res = result{}
	} else {
		res = result{found: s.present, value: s.value}
	}
	s.mu.Unlock()
	s.bmu.Lock()
	if !s.watched && s.watchCmd != "" && cmd == s.watchCmd {
		s.watched = true
		close(s.applied)
	}
	s.bmu.Unlock()
	return res
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

// --- the reads: hr3's readAt, way 2, without the client links (the test is the client), with a pause point

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

// readAt2: hr3's readAt for way 2; beforeRead (if not nil) runs after the final term check, before the FSM read
func readAt2(rs []*raft.Raft, st []*store, rd *readers, j int, beforeRead func()) (result, bool) {
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
	if beforeRead != nil {
		beforeRead()
	}
	return st[j].read(), true
}

func waitFor(t *testing.T, what string, d time.Duration, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(d)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(2 * time.Millisecond)
	}
}

func waitCh(t *testing.T, what string, d time.Duration, ch <-chan struct{}) {
	t.Helper()
	select {
	case <-ch:
	case <-time.After(d):
		t.Fatalf("timed out waiting for %s", what)
	}
}

func id(i int) raft.ServerID { return raft.ServerID(inproc.Addr(i)) }

// voters: the voters of server i's latest configuration
func voters(r *raft.Raft) ([]raft.ServerID, bool) {
	f := r.GetConfiguration()
	if err, ok := waitFuture(f); !ok || err != nil {
		return nil, false
	}
	var vs []raft.ServerID
	for _, s := range f.Configuration().Servers {
		if s.Suffrage == raft.Voter {
			vs = append(vs, s.ID)
		}
	}
	return vs, true
}

func TestVerifyLeaderSingleVoterFSMLag(t *testing.T) {
	nw := inproc.NewNet(n)
	var servers []raft.Server
	for i := 1; i <= n; i++ {
		servers = append(servers, raft.Server{Suffrage: raft.Voter, ID: id(i), Address: inproc.Addr(i)})
	}

	rs := make([]*raft.Raft, n+1)
	st := make([]*store, n+1)
	rd := &readers{barrierIn: make([]uint64, n+1)}
	for i := 1; i <= n; i++ {
		conf := raft.DefaultConfig()
		conf.LocalID = id(i)
		conf.HeartbeatTimeout = 100 * time.Millisecond
		conf.ElectionTimeout = 100 * time.Millisecond
		conf.LeaderLeaseTimeout = 100 * time.Millisecond
		conf.CommitTimeout = 5 * time.Millisecond
		conf.SnapshotThreshold = 1 << 62
		conf.ShutdownOnRemove = false
		logs := raft.NewInmemStore()
		stable := raft.NewInmemStore()
		snaps := raft.NewInmemSnapshotStore()
		trans := nw.Transport(i)
		if err := raft.BootstrapCluster(conf, logs, stable, snaps, trans, raft.Configuration{Servers: servers}); err != nil {
			t.Fatal(err)
		}
		st[i] = newStore()
		r, err := raft.NewRaft(conf, st[i], logs, stable, snaps, trans)
		if err != nil {
			t.Fatal(err)
		}
		rs[i] = r
	}
	resumeR1 := make(chan struct{})
	var releaseOnce sync.Once
	releaseK := func(s *store) { releaseOnce.Do(func() { close(s.release) }) }
	var kStore *store
	t.Cleanup(func() {
		select {
		case <-resumeR1:
		default:
			close(resumeR1)
		}
		if kStore != nil {
			releaseK(kStore)
		}
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

	// 1. j: the first leader
	var j int
	waitFor(t, "a leader", 10*time.Second, func() bool {
		for i := 1; i <= n; i++ {
			if rs[i].State() == raft.Leader {
				j = i
				return true
			}
		}
		return false
	})
	termJ := rs[j].CurrentTerm()
	k := j%n + 1 // the future only voter
	x := k%n + 1 // the third server

	// 2. r1 at j passes readAt's checks and pauses before reading j's FSM
	type readOut struct {
		res result
		ok  bool
	}
	r1Paused := make(chan struct{})
	r1Done := make(chan readOut, 1)
	go func() {
		res, ok := readAt2(rs, st, rd, j, func() {
			close(r1Paused)
			<-resumeR1
		})
		r1Done <- readOut{res, ok}
	}()
	select {
	case <-r1Paused:
	case out := <-r1Done:
		t.Fatalf("r1 at j failed its checks: %+v", out)
	case <-time.After(5 * time.Second):
		t.Fatal("timed out waiting for r1 to pass its checks at j")
	}
	if got := rs[j].CurrentTerm(); got != termJ {
		t.Fatalf("j's term moved from %d to %d", termJ, got)
	}

	// 3. at j: demote X, then j itself; j steps down once its demotion commits
	if err, ok := waitFuture(rs[j].DemoteVoter(id(x), 0, 0)); !ok || err != nil {
		t.Fatalf("DemoteVoter(S%d) at j (S%d): err=%v done=%v", x, j, err, ok)
	}
	// the outcome of j's own demotion: nil, or ErrLeadershipLost if j steps down before it answers
	if _, ok := waitFuture(rs[j].DemoteVoter(id(j), 0, 0)); !ok {
		t.Fatalf("DemoteVoter(S%d) at j did not return", j)
	}

	// 4. K, the only voter, is elected in a later term; j follows it
	waitFor(t, "K to lead alone in a later term", 10*time.Second, func() bool {
		if rs[k].State() != raft.Leader || rs[k].CurrentTerm() <= termJ {
			return false
		}
		vs, ok := voters(rs[k])
		return ok && len(vs) == 1 && vs[0] == id(k)
	})
	termK := rs[k].CurrentTerm()
	waitFor(t, "j to follow K", 10*time.Second, func() bool {
		addr, _ := rs[j].LeaderWithID()
		return rs[j].State() == raft.Follower && rs[j].CurrentTerm() == termK && addr == inproc.Addr(k)
	})

	// 5. r0 at K issues K's barrier of its term
	if res, ok := readAt2(rs, st, rd, k, nil); !ok || res.found {
		t.Fatalf("r0 at K (S%d): %+v ok=%v, want the empty register", k, res, ok)
	}
	rd.mu.Lock()
	if rd.barrierIn[k] != termK {
		t.Fatalf("K's barrier term is %d, want %d", rd.barrierIn[k], termK)
	}
	rd.mu.Unlock()

	// 6. K's FSM blocks its Apply of W; j's FSM reports when it has applied W; a client sends W to K
	const w = "Pw"
	kStore = st[k]
	st[k].bmu.Lock()
	st[k].blockCmd = w
	st[k].bmu.Unlock()
	st[j].bmu.Lock()
	st[j].watchCmd = w
	st[j].bmu.Unlock()
	wf := rs[k].Apply([]byte(w), 0) // its outcome stays unknown to the test (pending while the reads run)
	_ = wf
	waitCh(t, "K's FSM to reach W (W committed at K)", 5*time.Second, st[k].blocked)
	waitCh(t, "j to apply W", 10*time.Second, st[j].applied)

	// 7. r1 reads j's FSM and returns
	close(resumeR1)
	var r1 readOut
	select {
	case r1 = <-r1Done:
	case <-time.After(5 * time.Second):
		t.Fatal("timed out waiting for r1 to return")
	}
	if !r1.ok || !r1.res.found || r1.res.value != "w" {
		t.Fatalf("r1 at j returned %+v ok=%v, want \"w\"", r1.res, r1.ok)
	}
	t.Logf("r1 at j (S%d, checks passed in term %d) returned %q", j, termJ, r1.res.value)

	// 8. r2 at K, begun after r1 returned; K's FSM is released 300 ms later
	go func() {
		time.Sleep(300 * time.Millisecond)
		releaseK(st[k])
	}()
	r2, ok := readAt2(rs, st, rd, k, nil)
	if !ok {
		t.Fatalf("r2 at K (S%d) failed its checks (term now %d, state %v)", k, rs[k].CurrentTerm(), rs[k].State())
	}
	if rs[k].CurrentTerm() != termK {
		t.Fatalf("K's term moved from %d to %d", termK, rs[k].CurrentTerm())
	}
	if !r2.found || r2.value != "w" {
		t.Errorf("not linearizable: r1 at j (S%d) returned %q; r2 at the leader K (S%d, term %d, the only voter), "+
			"begun after r1 returned, passed every check of readAt (barrier of term %d applied, VerifyLeader nil, "+
			"term unchanged) and returned %+v (K's FSM had not applied W)", j, r1.res.value, k, termK, termK, r2)
	} else {
		t.Logf("r2 at K (S%d) returned %q", k, r2.value)
	}
}
