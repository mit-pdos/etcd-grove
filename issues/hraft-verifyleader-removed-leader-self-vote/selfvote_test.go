// Deterministic test for a VerifyLeader read at a leader that has removed (or demoted) itself, before that change
// commits. verifyLeader starts every verify with the leader's own vote (v.votes = 1) and the quorum of the latest
// configuration's voters. After RemoveServer or DemoteVoter of the leader itself, until that entry commits (only then
// does the leader step down), the leader leads a configuration it has no vote in: the commitment and the lease leave it
// out, but verifyLeader counts it. One voter's heartbeat response plus the leader's own (non-)vote then confirm it,
// while the other voters, a majority of the configuration in their logs, elect a leader that commits writes.
//
// Only the exported API is used. The test plays the clients itself, with examples/hr3's readAt (way 2) sequence of
// raft calls. The schedule is pinned by the network (inproc's one-direction cuts) and by waiting for each step.
//
// Scenario (servers S1..S4; S1 = L, S2 = V, S3 and S4 = A and B):
//  1. L is bootstrapped alone and elected in term T; it adds V, A and B as voters (four voters, quorum three).
//     Read r0 at L (way 2) applies L's Barrier of T and returns the empty register.
//  2. The links A->L and B->L are cut: from now on A's and B's responses to L are lost (L's requests still arrive).
//  3. L removes (or demotes) itself: the latest configuration is {V, A, B} as voters (quorum two). L sends the entry
//     to V, A and B; A and B append it, their acknowledgments are lost, so L's commitment (V only; L has no vote) never
//     reaches two: the entry stays uncommitted and L stays leader of term T.
//  4. The links L->A, L->B and V<->A, V<->B are cut: {L, V} | {A, B}. A and B (two of the three voters of the
//     configuration in their logs) elect a leader in term T+1, which commits and acknowledges a write W (Put "w").
//  5. Read r at L (way 2), begun after W was acknowledged: the barrier of T is applied (step 1); VerifyLeader counts
//     L's own vote and V's heartbeat response, 2 >= quorum 2, and returns nil; the term is still T; r reads L's FSM,
//     which does not have W.
//
// W was acknowledged before r began, so a linearizable r returns "w"; the test fails if r passes readAt's checks and
// misses W. With the fix (L's own vote counts only if L is a voter of its latest configuration) VerifyLeader has one
// vote of two; it waits until L's lease steps it down (then ErrNotLeader), and readAt gives up (hr3's waitFuture, 1 s):
// the read fails, which is allowed.
//
// L's LeaderLeaseTimeout is 2 s (its heartbeat timeout too, as the configuration requires), so that L keeps leading,
// as at any lease-respecting moment before its lease runs out, while A and B elect (their timeouts are lowered with
// ReloadConfig once they are cut off from L, to elect at once).
package verifyselfvotenonvotertest

import (
	"io"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
	"hraftissue/inproc"
)

const n = 4

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
func (s *store) Restore(rc io.ReadCloser) error       { return rc.Close() }

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

// readAt2: hr3's readAt for way 2; why: the step that failed, if any
func readAt2(rs []*raft.Raft, st []*store, rd *readers, j int) (res result, ok bool, why string) {
	r := rs[j]
	term := r.CurrentTerm()
	rd.mu.Lock()
	have := rd.barrierIn[j] == term
	rd.mu.Unlock()
	if !have {
		if err, ok := waitFuture(r.Barrier(100 * time.Millisecond)); !ok || err != nil {
			return result{}, false, "barrier"
		}
		if r.CurrentTerm() != term {
			return result{}, false, "term moved after the barrier"
		}
		rd.mu.Lock()
		rd.barrierIn[j] = term
		rd.mu.Unlock()
	}
	if err, ok := waitFuture(r.VerifyLeader()); !ok || err != nil {
		if !ok {
			return result{}, false, "VerifyLeader gave no answer within 1 s"
		}
		return result{}, false, "VerifyLeader: " + err.Error()
	}
	if r.CurrentTerm() != term {
		return result{}, false, "term moved after VerifyLeader"
	}
	return st[j].read(), true, ""
}

// --- helpers

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

func waitErr(t *testing.T, what string, d time.Duration, f raft.Future) {
	t.Helper()
	errCh := make(chan error, 1)
	go func() { errCh <- f.Error() }()
	select {
	case err := <-errCh:
		if err != nil {
			t.Fatalf("step did not happen: %s: %v", what, err)
		}
	case <-time.After(d):
		t.Fatalf("step did not happen: timed out waiting for %s", what)
	}
}

func id(i int) raft.ServerID { return raft.ServerID(inproc.Addr(i)) }

// latestHas: server i's latest configuration (in its log) has s as a voter
func latestVoter(r *raft.Raft, s int) bool {
	f := r.GetConfiguration()
	if f.Error() != nil {
		return false
	}
	for _, srv := range f.Configuration().Servers {
		if srv.ID == id(s) {
			return srv.Suffrage == raft.Voter
		}
	}
	return false
}

func TestVerifyLeaderSelfVoteRemoved(t *testing.T) { run(t, false) }
func TestVerifyLeaderSelfVoteDemoted(t *testing.T) { run(t, true) }

func run(t *testing.T, demote bool) {
	const l, v, a, b = 1, 2, 3, 4
	nw := inproc.NewNet(n)
	rs := make([]*raft.Raft, n+1)
	st := make([]*store, n+1)
	rd := &readers{barrierIn: make([]uint64, n+1)}
	for i := 1; i <= n; i++ {
		conf := raft.DefaultConfig()
		conf.LocalID = id(i)
		if i == l {
			// L's lease (and so its heartbeat timeout): long enough for A and B to elect and commit W
			conf.HeartbeatTimeout = 2 * time.Second
			conf.ElectionTimeout = 2 * time.Second
			conf.LeaderLeaseTimeout = 2 * time.Second
		} else {
			// longer than L's heartbeat interval (HeartbeatTimeout/10, up to twice that); A's and B's are lowered
			// with ReloadConfig in step 4 (to 200 ms, which their lease of 100 ms allows)
			conf.HeartbeatTimeout = time.Second
			conf.ElectionTimeout = time.Second
			conf.LeaderLeaseTimeout = 100 * time.Millisecond
		}
		conf.CommitTimeout = 5 * time.Millisecond
		conf.SnapshotThreshold = 1 << 62
		conf.ShutdownOnRemove = false
		logs := raft.NewInmemStore()
		stable := raft.NewInmemStore()
		snaps := raft.NewInmemSnapshotStore()
		trans := nw.Transport(i)
		if i == l {
			boot := raft.Configuration{Servers: []raft.Server{{Suffrage: raft.Voter, ID: id(l), Address: inproc.Addr(l)}}}
			if err := raft.BootstrapCluster(conf, logs, stable, snaps, trans, boot); err != nil {
				t.Fatal(err)
			}
		}
		st[i] = &store{}
		r, err := raft.NewRaft(conf, st[i], logs, stable, snaps, trans)
		if err != nil {
			t.Fatal(err)
		}
		rs[i] = r
	}
	type cut struct{ a, b int }
	var cuts []cut
	cutLink := func(x, y int) {
		nw.Cut(x, y, true)
		cuts = append(cuts, cut{x, y})
	}
	t.Cleanup(func() {
		for _, c := range cuts {
			nw.Cut(c.a, c.b, false)
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

	// 1. L leads term T with four voters; r0 at L applies L's barrier of T
	waitFor(t, "L to be elected", 10*time.Second, func() bool { return rs[l].State() == raft.Leader })
	for _, i := range []int{v, a, b} {
		waitErr(t, "AddVoter", 5*time.Second, rs[l].AddVoter(id(i), inproc.Addr(i), 0, 0))
	}
	for _, i := range []int{v, a, b} {
		i := i
		waitFor(t, "every server to hold the four voters", 5*time.Second, func() bool { return latestVoter(rs[i], b) })
	}
	termT := rs[l].CurrentTerm()
	if res, ok, why := readAt2(rs, st, rd, l); !ok || res.found {
		t.Fatalf("step did not happen: r0 at L: %+v ok=%v %s, want the empty register", res, ok, why)
	}
	if rs[l].CurrentTerm() != termT || rs[l].State() != raft.Leader {
		t.Fatalf("step did not happen: L left term %d", termT)
	}

	// 2. A's and B's responses to L are lost from now on
	cutLink(a, l)
	cutLink(b, l)

	// 3. L removes (or demotes) itself; A and B append the entry (their acknowledgments are lost)
	change := "RemoveServer"
	if demote {
		change = "DemoteVoter"
		_ = rs[l].DemoteVoter(id(l), 0, 0) // never commits in this run: not waited for
	} else {
		_ = rs[l].RemoveServer(id(l), 0, 0) // never commits in this run: not waited for
	}
	for _, i := range []int{l, a, b} {
		i := i
		waitFor(t, "L's "+change+" of itself in L's, A's and B's logs", 5*time.Second, func() bool {
			return !latestVoter(rs[i], l) && latestVoter(rs[i], v) && latestVoter(rs[i], a) && latestVoter(rs[i], b)
		})
	}

	// 4. {L, V} | {A, B}: A and B elect a leader of a later term, which commits and acknowledges W
	cutLink(l, a)
	cutLink(l, b)
	for _, x := range []int{a, b} {
		cutLink(v, x)
		cutLink(x, v)
		rc := rs[x].ReloadableConfig()
		rc.HeartbeatTimeout = 200 * time.Millisecond
		rc.ElectionTimeout = 200 * time.Millisecond
		if err := rs[x].ReloadConfig(rc); err != nil {
			t.Fatal(err)
		}
	}
	const w = "Pw"
	var k int
	acked := false
	deadline := time.Now().Add(5 * time.Second)
	for !acked {
		if time.Now().After(deadline) {
			t.Fatal("step did not happen: timed out waiting for A or B to commit W")
		}
		k = 0
		for _, x := range []int{a, b} {
			if rs[x].State() == raft.Leader && rs[x].CurrentTerm() > termT {
				k = x
			}
		}
		if k == 0 {
			time.Sleep(2 * time.Millisecond)
			continue
		}
		if err, ok := waitFuture(rs[k].Apply([]byte(w), 0)); ok && err == nil {
			acked = true
		} else if ok && err != raft.ErrNotLeader && err != raft.ErrLeadershipLost {
			// an outcome other than "not committed by this leader": W may or may not be in; stop here
			t.Fatalf("step did not happen: Apply of W at S%d: %v", k, err)
		} else if !ok {
			t.Fatalf("step did not happen: Apply of W at S%d gave no answer", k)
		}
	}
	termK := rs[k].CurrentTerm()
	t.Logf("W acknowledged by S%d, leader of term %d (configuration in its log: V, A, B; quorum two)", k, termK)
	if rs[l].State() != raft.Leader || rs[l].CurrentTerm() != termT {
		t.Fatalf("step did not happen: L (S%d) no longer leads term %d before the read (state %v, term %d)", l, termT,
			rs[l].State(), rs[l].CurrentTerm())
	}
	if latestVoter(rs[l], l) {
		t.Fatalf("step did not happen: L's latest configuration has L as a voter")
	}

	// 5. read r at L, begun after W was acknowledged
	res, ok, why := readAt2(rs, st, rd, l)
	if !ok {
		t.Logf("r at L (S%d) failed its checks (%s): no read returned; L now %v in term %d", l, why,
			rs[l].State(), rs[l].CurrentTerm())
		// and a VerifyLeader waited for to the end does not confirm L either (the lease steps it down)
		errCh := make(chan error, 1)
		go func() { errCh <- rs[l].VerifyLeader().Error() }()
		select {
		case err := <-errCh:
			if err == nil && rs[l].CurrentTerm() == termT {
				t.Errorf("stale leadership: VerifyLeader at L (S%d) returned nil in term %d after S%d led term %d and "+
					"acknowledged W", l, termT, k, termK)
			} else {
				t.Logf("VerifyLeader at L, waited for: %v", err)
			}
		case <-time.After(10 * time.Second):
			t.Fatal("step did not happen: VerifyLeader at L gave no answer within 10 s")
		}
		return
	}
	if !res.found || res.value != "w" {
		t.Errorf("stale read, not linearizable: W (Put \"w\") was acknowledged by S%d, leader of term %d, before r "+
			"began; r at L (S%d), which had appended its own %s and so is not a voter of its latest configuration, "+
			"passed every check of readAt way 2 (barrier of term %d applied, VerifyLeader nil, term unchanged) and "+
			"returned %+v", k, termK, l, change, termT, res)
	} else {
		t.Logf("r at L returned %q", res.value)
	}
}
