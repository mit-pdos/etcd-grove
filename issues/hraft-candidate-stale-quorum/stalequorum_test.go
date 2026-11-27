// Deterministic test for a candidate that counts its election's votes against the quorum of the configuration it had
// when its pre-vote began, not that of the configuration whose voters it asked.
//
// runCandidate computes votesNeeded := r.quorumSize() once, before the pre-vote. When the pre-vote is won it calls
// electSelf, which asks the voters of the latest configuration at that time. In between, the latest configuration can
// change: a TimeoutNow received during the pre-vote sets candidateFromLeadershipTransfer (and leaves the server a
// Candidate in the same runCandidate), after which appendEntries of the candidate's own term does not make it step
// down (a.Term > currentTerm || (state != Follower && !candidateFromLeadershipTransfer)) and stores the leader's
// entries, a configuration entry included. The votes are then counted against the old configuration's quorum.
//
// Only the exported API is used; the network is examples/inproc behind a wrapper that loses (or holds back and later
// delivers) the requests the schedule names. The schedule (servers S1..S6; L = S1, C = S2, D = S3):
//  1. L is bootstrapped alone, elected in term t, and adds S2..S5 as voters: O = {S1..S5} (quorum three), committed
//     everywhere. S6 runs, empty, not a member.
//  2. The network loses L's AppendEntries to C: C times out and becomes a Candidate; its pre-vote (for t+1, counted
//     against O: votesNeeded = 3) asks S1, S3, S4, S5; the requests to S3, S4, S5 are held back in the network. L
//     refuses (it leads).
//  3. L.LeadershipTransferToServer(C): L's TimeoutNow reaches C, which is already a Candidate: it stays in the same
//     runCandidate (still in the pre-vote, votesNeeded still 3) with candidateFromLeadershipTransfer set. The
//     transfer times out at L (L keeps leading t).
//  4. L's AppendEntries carrying entries to S3, S4, S5 are lost (heartbeats still arrive); L's AppendEntries to C get
//     through again. L.AddVoter(S6): N = {S1..S6} (quorum four) at index i, term t, reaches C and S6 only. C accepts
//     it in term t though it is a Candidate (the flag) and its latest configuration becomes N.
//  5. Partition {S1, S2, S6} | {S3, S4, S5}, and inside the second group every link is cut except, from step 7,
//     S3<->S4 and S3<->S5 (so that only S3 can win there). S3, S4, S5 time out and become Candidates (no known leader).
//  6. C's held pre-vote requests reach S4 and S5 (two messages delayed in the network), which grant them (no leader,
//     C's log as up to date): C has 3 >= votesNeeded pre-votes and calls electSelf for t+1, asking N's voters
//     S1, S3, S4, S5, S6. S1 and S6 grant (the request carries LeadershipTransfer); the others are lost. C has three
//     votes, which are not a majority of N (four of six) but are >= the stale votesNeeded = 3: C leads term t+1.
//  7. S3<->S4, S3<->S5 open: S3, S4, S5 (O, without the entry at i: quorum three) elect S3 in term t+1.
//
// Two leaders in term t+1: election safety violated. With the fix (votesNeeded recomputed when electSelf is called
// after the pre-vote) C needs four votes of N, has three, and stays a Candidate: one leader in t+1.
package candidatestalequorumtest

import (
	"fmt"
	"io"
	"sort"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
	"hraftissue/inproc"
)

const n = 6

const (
	sL = 1 // the leader of term t
	sC = 2 // the candidate that receives TimeoutNow during its pre-vote
	sD = 3 // the leader of term t+1 on the other side
)

// --- the FSM: nothing (the test checks election safety)

type nopFSM struct{}

func (nopFSM) Apply(*raft.Log) interface{}         { return nil }
func (nopFSM) Snapshot() (raft.FSMSnapshot, error) { return nopSnap{}, nil }
func (nopFSM) Restore(rc io.ReadCloser) error      { return rc.Close() }

type nopSnap struct{}

func (nopSnap) Persist(sink raft.SnapshotSink) error { return sink.Close() }
func (nopSnap) Release()                             {}

// --- the network: inproc behind a wrapper that loses the requests the phase says are lost

const (
	phaseOpen      = iota // nothing lost
	phaseCutC             // L's AppendEntries to C lost
	phaseHoldBack         // L's AppendEntries carrying entries to S3, S4, S5 lost
	phasePartition        // {S1, S2, S6} | {S3, S4, S5}, every link inside the second group cut
	phaseElectD           // as phasePartition, but S3<->S4 and S3<->S5 open
)

type network struct {
	mu    sync.Mutex
	phase int
	// C's pre-vote requests to S3, S4, S5 are held back until released (deliver or lose)
	hold    bool
	gates   map[int]chan struct{}
	deliver map[int]bool
	// a TimeoutNow from L reached C
	timeoutNowDelivered bool
}

func group(i int) int {
	if i == 3 || i == 4 || i == 5 {
		return 1
	}
	return 0
}

// lost: a request from a to b is lost in the current phase
func (nw *network) lost(a, b int, req interface{}) bool {
	nw.mu.Lock()
	phase := nw.phase
	nw.mu.Unlock()
	switch phase {
	case phaseCutC:
		_, ae := req.(*raft.AppendEntriesRequest)
		return a == sL && b == sC && ae
	case phaseHoldBack:
		r, ae := req.(*raft.AppendEntriesRequest)
		return a == sL && group(b) == 1 && ae && len(r.Entries) > 0
	case phasePartition, phaseElectD:
		if group(a) != group(b) {
			return true
		}
		if group(a) == 1 {
			if phase == phaseElectD && (a == sD || b == sD) {
				return false
			}
			return true
		}
	}
	return false
}

// holdPreVote: called for C's pre-vote request to b; blocks while it is held back. Returns whether the request is
// delivered (true) or lost (false); held is false if it was never held.
func (nw *network) holdPreVote(b int) (deliver bool, held bool) {
	nw.mu.Lock()
	if !nw.hold || group(b) != 1 {
		nw.mu.Unlock()
		return false, false
	}
	g, ok := nw.gates[b]
	if !ok {
		g = make(chan struct{})
		nw.gates[b] = g
	}
	nw.mu.Unlock()
	<-g
	nw.mu.Lock()
	defer nw.mu.Unlock()
	return nw.deliver[b], true
}

// release: C's held pre-vote request to b (and any later one) is delivered or lost
func (nw *network) release(b int, deliver bool) {
	nw.mu.Lock()
	defer nw.mu.Unlock()
	nw.deliver[b] = deliver
	g, ok := nw.gates[b]
	if !ok {
		g = make(chan struct{})
		nw.gates[b] = g
	}
	select {
	case <-g:
	default:
		close(g)
	}
}

func (nw *network) setPhase(p int) {
	nw.mu.Lock()
	nw.phase = p
	nw.mu.Unlock()
}

type transport struct {
	*inproc.Transport
	i  int
	nw *network
}

func idx(a raft.ServerAddress) int {
	var k int
	fmt.Sscanf(string(a), "%d", &k)
	return k
}

// AppendEntriesPipeline: no pipeline, so that every AppendEntries goes through the wrapper (raft falls back to
// AppendEntries, as for any transport without pipelining)
func (t *transport) AppendEntriesPipeline(id raft.ServerID, target raft.ServerAddress) (raft.AppendPipeline, error) {
	return nil, raft.ErrPipelineReplicationNotSupported
}

func (t *transport) AppendEntries(id raft.ServerID, target raft.ServerAddress, args *raft.AppendEntriesRequest,
	resp *raft.AppendEntriesResponse) error {
	if t.nw.lost(t.i, idx(target), args) {
		return inproc.ErrCut
	}
	return t.Transport.AppendEntries(id, target, args, resp)
}

func (t *transport) RequestVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestVoteRequest,
	resp *raft.RequestVoteResponse) error {
	if t.nw.lost(t.i, idx(target), args) {
		return inproc.ErrCut
	}
	return t.Transport.RequestVote(id, target, args, resp)
}

func (t *transport) RequestPreVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestPreVoteRequest,
	resp *raft.RequestPreVoteResponse) error {
	if t.i == sC {
		if deliver, held := t.nw.holdPreVote(idx(target)); held {
			if !deliver {
				return inproc.ErrCut
			}
			// a request delayed in the network, delivered now
			return t.Transport.RequestPreVote(id, target, args, resp)
		}
	}
	if t.nw.lost(t.i, idx(target), args) {
		return inproc.ErrCut
	}
	return t.Transport.RequestPreVote(id, target, args, resp)
}

func (t *transport) TimeoutNow(id raft.ServerID, target raft.ServerAddress, args *raft.TimeoutNowRequest,
	resp *raft.TimeoutNowResponse) error {
	if t.nw.lost(t.i, idx(target), args) {
		return inproc.ErrCut
	}
	err := t.Transport.TimeoutNow(id, target, args, resp)
	if err == nil && t.i == sL && idx(target) == sC {
		t.nw.mu.Lock()
		t.nw.timeoutNowDelivered = true
		t.nw.mu.Unlock()
	}
	return err
}

func (t *transport) InstallSnapshot(id raft.ServerID, target raft.ServerAddress, args *raft.InstallSnapshotRequest,
	resp *raft.InstallSnapshotResponse, data io.Reader) error {
	if t.nw.lost(t.i, idx(target), args) {
		return inproc.ErrCut
	}
	return t.Transport.InstallSnapshot(id, target, args, resp, data)
}

// --- the leaders of each term, as observed (a server is leader of term x when CurrentTerm reads x before and after
// State reads Leader: a server's term does not change while it leads)

type leaders struct {
	mu sync.Mutex
	of map[uint64]map[int]bool
}

func (l *leaders) watch(rs []*raft.Raft, stop chan struct{}, done chan struct{}) {
	defer close(done)
	for {
		select {
		case <-stop:
			return
		default:
		}
		for i := 1; i <= n; i++ {
			t1 := rs[i].CurrentTerm()
			s := rs[i].State()
			t2 := rs[i].CurrentTerm()
			if s == raft.Leader && t1 == t2 {
				l.mu.Lock()
				if l.of[t1] == nil {
					l.of[t1] = map[int]bool{}
				}
				l.of[t1][i] = true
				l.mu.Unlock()
			}
		}
		time.Sleep(time.Millisecond)
	}
}

func (l *leaders) in(term uint64) []int {
	l.mu.Lock()
	defer l.mu.Unlock()
	var out []int
	for i := range l.of[term] {
		out = append(out, i)
	}
	sort.Ints(out)
	return out
}

// --- helpers

var dump func() string

func waitFor(t *testing.T, what string, d time.Duration, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(d)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("step did not happen: timed out waiting for %s; %s", what, dump())
		}
		time.Sleep(2 * time.Millisecond)
	}
}

func id(i int) raft.ServerID { return raft.ServerID(inproc.Addr(i)) }

// voters: server r's latest configuration's voters
func voters(r *raft.Raft) []int {
	f := r.GetConfiguration()
	if f.Error() != nil {
		return nil
	}
	var out []int
	for _, s := range f.Configuration().Servers {
		if s.Suffrage == raft.Voter {
			out = append(out, idx(s.Address))
		}
	}
	sort.Ints(out)
	return out
}

func hasVoter(r *raft.Raft, s int) bool {
	for _, v := range voters(r) {
		if v == s {
			return true
		}
	}
	return false
}

func TestCandidateStaleQuorum(t *testing.T) {
	inet := inproc.NewNet(n)
	nw := &network{gates: map[int]chan struct{}{}, deliver: map[int]bool{}}
	rs := make([]*raft.Raft, n+1)
	for i := 1; i <= n; i++ {
		conf := raft.DefaultConfig()
		conf.LocalID = id(i)
		if i == sL {
			// heartbeats every 50-100 ms; the leadership transfer gives up after 500 ms
			conf.HeartbeatTimeout = 500 * time.Millisecond
			conf.ElectionTimeout = 500 * time.Millisecond
			conf.LeaderLeaseTimeout = 500 * time.Millisecond
		} else {
			conf.HeartbeatTimeout = 300 * time.Millisecond
			conf.ElectionTimeout = 300 * time.Millisecond
			conf.LeaderLeaseTimeout = 300 * time.Millisecond
		}
		if i == sC {
			// C's election timer (runCandidate) does not run out during the test: one candidacy, one pre-vote
			conf.ElectionTimeout = 30 * time.Second
		}
		conf.CommitTimeout = 5 * time.Millisecond
		conf.SnapshotThreshold = 1 << 62
		conf.SnapshotInterval = time.Hour
		conf.ShutdownOnRemove = false
		logs := raft.NewInmemStore()
		stable := raft.NewInmemStore()
		snaps := raft.NewInmemSnapshotStore()
		trans := &transport{Transport: inet.Transport(i), i: i, nw: nw}
		if i == sL {
			boot := raft.Configuration{Servers: []raft.Server{{Suffrage: raft.Voter, ID: id(sL), Address: inproc.Addr(sL)}}}
			if err := raft.BootstrapCluster(conf, logs, stable, snaps, trans, boot); err != nil {
				t.Fatal(err)
			}
		}
		r, err := raft.NewRaft(conf, nopFSM{}, logs, stable, snaps, trans)
		if err != nil {
			t.Fatal(err)
		}
		rs[i] = r
	}
	dump = func() string {
		var b strings.Builder
		for i := 1; i <= n; i++ {
			fmt.Fprintf(&b, "S%d: %v term %d last %d voters %v; ", i, rs[i].State(), rs[i].CurrentTerm(),
				rs[i].LastIndex(), voters(rs[i]))
		}
		return b.String()
	}
	ld := &leaders{of: map[uint64]map[int]bool{}}
	stop, watched := make(chan struct{}), make(chan struct{})
	go ld.watch(rs, stop, watched)
	t.Cleanup(func() {
		close(stop)
		<-watched
		for b := 1; b <= n; b++ {
			nw.release(b, false)
		}
		nw.setPhase(phaseOpen)
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

	// 1. L leads term t of O = {S1..S5}; every entry committed on S1..S5
	waitFor(t, "L to be elected", 10*time.Second, func() bool { return rs[sL].State() == raft.Leader })
	for i := 2; i <= 5; i++ {
		if err := rs[sL].AddVoter(id(i), inproc.Addr(i), 0, 0).Error(); err != nil {
			t.Fatalf("step did not happen: AddVoter S%d: %v", i, err)
		}
	}
	termT := rs[sL].CurrentTerm()
	waitFor(t, "S1..S5 to hold and apply L's whole log in term t", 5*time.Second, func() bool {
		last := rs[sL].LastIndex()
		for i := 1; i <= 5; i++ {
			if rs[i].LastIndex() != last || rs[i].AppliedIndex() != last || rs[i].CurrentTerm() != termT ||
				len(voters(rs[i])) != 5 {
				return false
			}
		}
		return rs[sL].State() == raft.Leader
	})
	t.Logf("L = S%d leads term %d of O = %v", sL, termT, voters(rs[sL]))

	// 2. L's AppendEntries to C lost: C becomes a Candidate; its pre-vote requests to S3, S4, S5 are held back
	nw.mu.Lock()
	nw.hold = true
	nw.mu.Unlock()
	nw.setPhase(phaseCutC)
	waitFor(t, "C to become a Candidate (pre-vote)", 5*time.Second, func() bool { return rs[sC].State() == raft.Candidate })
	if rs[sC].CurrentTerm() != termT {
		t.Fatalf("step did not happen: C's term moved to %d during its pre-vote", rs[sC].CurrentTerm())
	}

	// 3. L transfers leadership to C: TimeoutNow reaches C while it is in its pre-vote; the transfer times out at L
	tf := rs[sL].LeadershipTransferToServer(id(sC), inproc.Addr(sC))
	waitFor(t, "L's TimeoutNow to reach C", 5*time.Second, func() bool {
		nw.mu.Lock()
		defer nw.mu.Unlock()
		return nw.timeoutNowDelivered
	})
	terr := tf.Error()
	t.Logf("leadership transfer at L: %v", terr)
	if rs[sL].State() != raft.Leader || rs[sL].CurrentTerm() != termT || rs[sC].State() != raft.Candidate ||
		rs[sC].CurrentTerm() != termT {
		t.Fatalf("step did not happen: after the TimeoutNow, L should lead term %d and C be a Candidate in its pre-vote; %s",
			termT, dump())
	}

	// 4. entries to S3, S4, S5 lost; L adds S6 as a voter: the entry reaches C (a Candidate, flag set) and S6
	nw.setPhase(phaseHoldBack)
	deadline := time.Now().Add(5 * time.Second)
	for {
		f := rs[sL].AddVoter(id(6), inproc.Addr(6), 0, 0) // never commits in this run: not waited for beyond the check
		errCh := make(chan error, 1)
		go func() { errCh <- f.Error() }()
		var err error
		select {
		case err = <-errCh:
		case <-time.After(100 * time.Millisecond):
		}
		if err != raft.ErrLeadershipTransferInProgress {
			if err != nil {
				t.Fatalf("step did not happen: AddVoter S6: %v", err)
			}
			break
		}
		if time.Now().After(deadline) {
			t.Fatal("step did not happen: L kept refusing AddVoter (leadership transfer in progress)")
		}
		time.Sleep(5 * time.Millisecond)
	}
	waitFor(t, "L, C and S6 to hold N = {S1..S6}", 5*time.Second, func() bool {
		return hasVoter(rs[sL], 6) && hasVoter(rs[sC], 6) && hasVoter(rs[6], 6)
	})
	if rs[sC].State() != raft.Candidate || rs[sC].CurrentTerm() != termT {
		t.Fatalf("step did not happen: C left its candidacy of the pre-vote; %s", dump())
	}
	t.Logf("C (S%d), a Candidate in its pre-vote since before the AddVoter, now holds N = %v", sC, voters(rs[sC]))

	// 5. partition; S3, S4, S5 lose their leader
	nw.setPhase(phasePartition)
	waitFor(t, "S3, S4, S5 to become Candidates", 5*time.Second, func() bool {
		return rs[3].State() == raft.Candidate && rs[4].State() == raft.Candidate && rs[5].State() == raft.Candidate
	})
	for i := 3; i <= 5; i++ {
		if rs[i].CurrentTerm() != termT || hasVoter(rs[i], 6) {
			t.Fatalf("step did not happen: S%d should be in term %d without the AddVoter S6 entry; %s", i, termT, dump())
		}
	}

	// 6. C's held pre-vote requests reach S4 and S5: C wins the pre-vote and asks N's voters for term t+1
	nw.release(4, true)
	nw.release(5, true)
	waitFor(t, "C to win its pre-vote and start its election of term t+1", 5*time.Second, func() bool {
		return rs[sC].CurrentTerm() == termT+1
	})
	waitFor(t, "S1 and S6 to vote in term t+1", 5*time.Second, func() bool {
		return rs[sL].CurrentTerm() == termT+1 && rs[6].CurrentTerm() == termT+1
	})
	time.Sleep(300 * time.Millisecond)
	cLed := false
	for _, s := range ld.in(termT + 1) {
		if s == sC {
			cLed = true
		}
	}
	t.Logf("C led term %d: %v (its latest configuration N = %v needs 4 votes; it could get only its own, S1's and S6's)",
		termT+1, cLed, voters(rs[sC]))

	// 7. S3 is elected in term t+1 by S3, S4, S5 (O's quorum; their logs lack the AddVoter S6 entry)
	nw.setPhase(phaseElectD)
	waitFor(t, "S3 to lead term t+1", 10*time.Second, func() bool {
		for _, s := range ld.in(termT + 1) {
			if s == sD {
				return true
			}
		}
		return false
	})
	t.Logf("S%d leads term %d with configuration %v", sD, termT+1, voters(rs[sD]))

	if got := ld.in(termT + 1); len(got) > 1 {
		t.Errorf("election safety violated: servers %v were each leader of term %d. S%d won with three votes (its own, "+
			"S%d's and S6's), counted against the quorum of O = {S1..S5} (three) computed before its pre-vote, though it "+
			"asked the voters of N = {S1..S6} (quorum four), stored during the pre-vote after a TimeoutNow; S%d won with "+
			"S3, S4, S5, a majority of O, the configuration in their logs",
			got, termT+1, sC, sL, sD)
	}
}
