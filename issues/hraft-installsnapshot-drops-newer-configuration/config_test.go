// Deterministic test for state-machine safety across InstallSnapshot with a configuration change in flight. A
// follower that installs a leader's snapshot and keeps its log (the log holds the snapshot's last entry: Raft, Fig. 13
// step 6) must keep using the latest configuration in its log (Raft: a server uses the latest configuration in its
// log, committed or not). installSnapshot (raft.go) sets the latest configuration to the snapshot's, which is the
// sender's committed configuration, at or below the snapshot's index; a newer configuration entry after the snapshot,
// in the kept log, is no longer used (and later AppendEntries that carry it match and skip it). The follower then
// counts votes and commitment in the older configuration: it leads with too few votes and commits entries
// acknowledged by too few servers, while the others, with one more change, commit different entries at the same
// indexes.
//
// Only the exported API is used: raft.InmemStores, examples/snapstore, examples/inproc (partitions) wrapped in a
// raft.Transport that loses chosen AppendEntries requests or their responses and offers no pipeline, AddVoter,
// RemoveServer, Snapshot, GetConfiguration, and a user FSM whose state is the list of (index, command) pairs it
// applied. Every server's applies and restores are also recorded outside the FSM.
//
// Configuration (all servers): MaxAppendEntries M = 4, TrailingLogs 0, snapshots only when the test calls
// Snapshot(), timeouts 100 ms, pre-vote on (the default).
//
// Scenario (servers 1..3 the first configuration's voters C1 = {L, A, F}; server 4 = X starts as a non-member; p is
// the common prefix: the bootstrap configuration and L's no-op; S = p+M):
//  1. L, the first server elected, leads T1; L, A and F hold 1..p, committed.
//  2. The network loses L's AppendEntries with entries to A (heartbeats pass). L appends c1 at p+1 and commits it
//     with F (C1). Then it also loses those to F. L appends c2..cM at p+2..S and AddVoter X: C2 = {L, A, F, X} at
//     S+1 (latest at L; X catches up). Nothing commits beyond p+1: C2 needs three of L, A, F, X.
//  3. L's AppendEntries to F (next index p+2: entries p+2..S+1, commit index p+1) reach F, their responses are lost;
//     then F's requests are lost again. F holds S+1 (C2 is its latest configuration), committed p+1; L still sends
//     from p+2.
//  4. A's link opens except for requests with entries past S: L sends A p+1..S (a batch of M), A acknowledges S;
//     with X, L commits S (not S+1: A and X are two of C2's four; F's acknowledgements never arrived). L takes a
//     snapshot at S, whose configuration is the committed one, C1, and compacts its log up to S.
//  5. F's link opens: L misses entry p+1 and sends its snapshot. F (applied p+1 < S) installs it; F holds (S, T1)
//     and keeps its log, with C2 at S+1. At the code as given F's latest configuration is now C1 (GetConfiguration
//     shows it) though C2 is in its log; L's next AppendEntries (previous entry S, entry S+1) match and skip it.
//  6. A's link opens: A stores S+1; C2 commits (L, A, X; with F too).
//  7. The network loses L's AppendEntries with entries past S+1 to A and F. L removes A: C3 = {L, F, X} at S+2,
//     committed with X; L applies b at S+3, committed with X.
//  8. {L, X} | {F, A}. F, with C1, needs two votes: its own and A's (A's log ends at S+1 too). F leads, appends its
//     no-op at S+2 and c at S+3, and commits them with A (two of C1; two of C2's four, which is no quorum). F and A
//     apply c at S+3 where L and X applied b.
//
// The test fails (t.Errorf) if two servers applied different commands at one index; it fails with t.Fatal if a
// scheduled step does not happen. With the fix (installSnapshot scans the kept entries after the snapshot for
// configuration entries) F's latest configuration after step 5 is C2, in which F and A are two of four: step 8 elects
// no one in {F, A}; the test waits 3 s, sees no leader there, and finds no violation.
package snapshotinstallconfigtest

import (
	"encoding/json"
	"fmt"
	"io"
	"sort"
	"strconv"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
	"hraftissue/inproc"
	"hraftissue/snapstore"
)

const (
	nNet             = 4 // servers 1..3 voters, 4 = X (non-member at start)
	nVoters          = 3
	maxAppendEntries = 4
	trailingLogs     = 0
)

// --- the FSM: the list of (index, command) pairs applied; Restore replaces it

type entry struct {
	Index uint64
	Cmd   string
}

// event: one server's apply (or restore) of a command at an index, recorded outside the FSM
type event struct {
	server  int
	index   uint64
	cmd     string
	restore bool
}

type recorder struct {
	mu     sync.Mutex
	events []event
}

func (r *recorder) add(e event) {
	r.mu.Lock()
	r.events = append(r.events, e)
	r.mu.Unlock()
}

func (r *recorder) all() []event {
	r.mu.Lock()
	defer r.mu.Unlock()
	return append([]event(nil), r.events...)
}

type listFSM struct {
	id  int
	rec *recorder
	mu  sync.Mutex
	got []entry
}

func (f *listFSM) Apply(l *raft.Log) interface{} {
	f.mu.Lock()
	f.got = append(f.got, entry{l.Index, string(l.Data)})
	f.mu.Unlock()
	f.rec.add(event{server: f.id, index: l.Index, cmd: string(l.Data)})
	return nil
}

func (f *listFSM) Snapshot() (raft.FSMSnapshot, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	return listSnap(append([]entry(nil), f.got...)), nil
}

func (f *listFSM) Restore(rc io.ReadCloser) error {
	defer rc.Close()
	b, err := inproc.ReadAll(rc)
	if err != nil {
		return err
	}
	var got []entry
	if err := json.Unmarshal(b, &got); err != nil {
		return err
	}
	f.mu.Lock()
	f.got = got
	f.mu.Unlock()
	for _, e := range got {
		f.rec.add(event{server: f.id, index: e.Index, cmd: e.Cmd, restore: true})
	}
	return nil
}

type listSnap []entry

func (s listSnap) Persist(sink raft.SnapshotSink) error {
	b, err := json.Marshal([]entry(s))
	if err != nil {
		sink.Cancel()
		return err
	}
	if _, err := sink.Write(b); err != nil {
		sink.Cancel()
		return err
	}
	return sink.Close()
}

func (listSnap) Release() {}

// --- the network: partitions over inproc's nesting cuts

type links struct {
	nw  *inproc.Net
	cut [nNet + 1][nNet + 1]bool
}

func (l *links) set(a, b int, on bool) {
	if l.cut[a][b] != on {
		l.cut[a][b] = on
		l.nw.Cut(a, b, on)
	}
}

// partition: cut every link (both directions) between servers in different groups, open the others
func (l *links) partition(group [nNet + 1]int) {
	for a := 1; a <= nNet; a++ {
		for b := 1; b <= nNet; b++ {
			if a != b {
				l.set(a, b, group[a] != group[b])
			}
		}
	}
}

// what the network does with one AppendEntries request
type fate int

const (
	deliver      fate = iota
	loseRequest       // the request is lost (the call fails, as on a cut link)
	loseResponse      // the request is delivered and handled, its response is lost (the call fails)
)

// filterTransport: inproc's transport, which loses the AppendEntries requests (or their responses) the test asks
// it to, and offers no pipeline (every AppendEntries goes through replicateTo, one at a time)
type filterTransport struct {
	*inproc.Transport
	mu     sync.Mutex
	filter func(target int, req *raft.AppendEntriesRequest) fate
}

func (t *filterTransport) setFilter(f func(target int, req *raft.AppendEntriesRequest) fate) {
	t.mu.Lock()
	t.filter = f
	t.mu.Unlock()
}

func addrIndex(a raft.ServerAddress) int {
	i, err := strconv.Atoi(string(a))
	if err != nil {
		panic(err)
	}
	return i
}

func (t *filterTransport) AppendEntries(id raft.ServerID, target raft.ServerAddress, args *raft.AppendEntriesRequest,
	resp *raft.AppendEntriesResponse) error {
	t.mu.Lock()
	f := t.filter
	t.mu.Unlock()
	what := deliver
	if f != nil {
		what = f(addrIndex(target), args)
	}
	switch what {
	case loseRequest:
		return inproc.ErrCut
	case loseResponse:
		var lost raft.AppendEntriesResponse
		_ = t.Transport.AppendEntries(id, target, args, &lost)
		return inproc.ErrCut
	}
	return t.Transport.AppendEntries(id, target, args, resp)
}

func (t *filterTransport) AppendEntriesPipeline(id raft.ServerID, target raft.ServerAddress) (raft.AppendPipeline, error) {
	return nil, raft.ErrPipelineReplicationNotSupported
}

// lastEntry: the index of a request's last entry (0 for none)
func lastEntry(req *raft.AppendEntriesRequest) uint64 {
	if len(req.Entries) == 0 {
		return 0
	}
	return req.Entries[len(req.Entries)-1].Index
}

// dump: every server's state, logged when a scheduled step does not happen
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

// servers: a configuration's servers as "S<i>:<suffrage>"
func servers(c raft.Configuration) []string {
	var out []string
	for _, s := range c.Servers {
		out = append(out, fmt.Sprintf("S%s:%v", s.ID, s.Suffrage))
	}
	sort.Strings(out)
	return out
}

func hasServer(c raft.Configuration, i int) bool {
	for _, s := range c.Servers {
		if s.ID == id(i) {
			return true
		}
	}
	return false
}

func TestSnapshotInstallKeepsOlderConfiguration(t *testing.T) {
	nw := inproc.NewNet(nNet)
	ln := &links{nw: nw}
	var voters []raft.Server
	for i := 1; i <= nVoters; i++ {
		voters = append(voters, raft.Server{Suffrage: raft.Voter, ID: id(i), Address: inproc.Addr(i)})
	}

	rec := &recorder{}
	rs := make([]*raft.Raft, nNet+1)
	logs := make([]*raft.InmemStore, nNet+1)
	snaps := make([]*snapstore.Store, nNet+1)
	transports := make([]*filterTransport, nNet+1)
	for i := 1; i <= nNet; i++ {
		conf := raft.DefaultConfig()
		conf.LocalID = id(i)
		conf.HeartbeatTimeout = 100 * time.Millisecond
		conf.ElectionTimeout = 100 * time.Millisecond
		conf.LeaderLeaseTimeout = 100 * time.Millisecond
		conf.CommitTimeout = 5 * time.Millisecond
		conf.MaxAppendEntries = maxAppendEntries
		conf.TrailingLogs = trailingLogs
		conf.SnapshotThreshold = 1 << 62
		conf.SnapshotInterval = time.Hour
		logs[i] = raft.NewInmemStore()
		stable := raft.NewInmemStore()
		snaps[i] = snapstore.New()
		trans := &filterTransport{Transport: nw.Transport(i)}
		transports[i] = trans
		if i <= nVoters {
			if err := raft.BootstrapCluster(conf, logs[i], stable, snaps[i], trans, raft.Configuration{Servers: voters}); err != nil {
				t.Fatal(err)
			}
		}
		r, err := raft.NewRaft(conf, &listFSM{id: i, rec: rec}, logs[i], stable, snaps[i], trans)
		if err != nil {
			t.Fatal(err)
		}
		rs[i] = r
	}
	t.Cleanup(func() {
		for i := 1; i <= nNet; i++ {
			transports[i].setFilter(nil)
		}
		ln.partition([nNet + 1]int{})
		done := make(chan struct{})
		go func() {
			for i := 1; i <= nNet; i++ {
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

	dump = func() string {
		out := "servers:"
		for i := 1; i <= nNet; i++ {
			out += fmt.Sprintf(" S%d{%v term %d last %d commit %d applied %d}", i, rs[i].State(), rs[i].CurrentTerm(),
				rs[i].LastIndex(), rs[i].CommitIndex(), rs[i].AppliedIndex())
		}
		return out
	}
	leaderAmong := func(set []int, minTerm uint64) int {
		for _, i := range set {
			if rs[i].State() == raft.Leader && rs[i].CurrentTerm() > minTerm {
				return i
			}
		}
		return 0
	}
	configOf := func(i int) raft.Configuration {
		fu := rs[i].GetConfiguration()
		if err := fu.Error(); err != nil {
			t.Fatalf("S%d's GetConfiguration: %v", i, err)
		}
		return fu.Configuration()
	}
	// logStore: the entries of server i's log store in [lo, hi], as index:term:data
	logStore := func(i int, lo, hi uint64) []string {
		var out []string
		for j := lo; j <= hi; j++ {
			var l raft.Log
			if err := logs[i].GetLog(j, &l); err == nil {
				data := fmt.Sprintf("%q", l.Data)
				if l.Type == raft.LogConfiguration {
					data = fmt.Sprintf("%v", servers(raft.DecodeConfiguration(l.Data)))
				} else if l.Type != raft.LogCommand {
					data = l.Type.String()
				}
				out = append(out, fmt.Sprintf("%d:t%d:%s", l.Index, l.Term, data))
			} else {
				out = append(out, fmt.Sprintf("%d:-", j))
			}
		}
		return out
	}
	stillLeads := func(l int, term uint64) {
		t.Helper()
		if rs[l].State() != raft.Leader || rs[l].CurrentTerm() != term {
			t.Fatalf("step did not happen: L (S%d) lost leadership of term %d; %s", l, term, dump())
		}
	}
	all := []int{1, 2, 3}
	const x = 4

	// 1. L leads T1; L, A and F hold 1..p, committed
	var l int
	waitFor(t, "a first leader", 10*time.Second, func() bool { l = leaderAmong(all, 0); return l != 0 })
	termL := rs[l].CurrentTerm()
	waitFor(t, "L's no-op to commit at every voter", 5*time.Second, func() bool {
		p := rs[l].LastIndex()
		for _, i := range all {
			if rs[i].LastIndex() != p || rs[i].CurrentTerm() != termL {
				return false
			}
		}
		return p > 1 && rs[l].CommitIndex() == p
	})
	stillLeads(l, termL)
	p := rs[l].LastIndex()
	s := p + maxAppendEntries
	f := l%nVoters + 1
	a := f%nVoters + 1
	t.Logf("L=S%d (term %d), F=S%d, A=S%d, X=S%d; prefix 1..%d, snapshot index S=%d", l, termL, f, a, x, p, s)

	// 2. lose L's AppendEntries with entries to A; c1 commits with F; then lose those to F too; L appends c2..cM and
	// AddVoter X (C2 at S+1)
	var mu sync.Mutex
	fateA, fateF := loseRequest, deliver
	var aLimit uint64 // with fateA == deliver: lose requests to A with entries past aLimit (0: none)
	transports[l].setFilter(func(target int, req *raft.AppendEntriesRequest) fate {
		if len(req.Entries) == 0 {
			return deliver // heartbeats, and the probes after a snapshot
		}
		mu.Lock()
		defer mu.Unlock()
		switch target {
		case a:
			if fateA == deliver && aLimit != 0 && lastEntry(req) > aLimit {
				return loseRequest
			}
			return fateA
		case f:
			return fateF
		}
		return deliver
	})
	setFates := func(fa, ff fate, limit uint64) {
		mu.Lock()
		fateA, fateF, aLimit = fa, ff, limit
		mu.Unlock()
	}
	if err := rs[l].Apply([]byte("c1"), 0).Error(); err != nil {
		t.Fatalf("step did not happen: L's c1: %v; %s", err, dump())
	}
	q := p + 1
	waitFor(t, "F to hold c1 and L to commit it", 5*time.Second, func() bool {
		return rs[l].CommitIndex() == q && rs[f].LastIndex() == q
	})
	setFates(loseRequest, loseRequest, 0)
	var futs []raft.ApplyFuture
	for k := 2; k <= maxAppendEntries; k++ {
		futs = append(futs, rs[l].Apply([]byte(fmt.Sprintf("c%d", k)), 0))
	}
	waitFor(t, "L to append c2..cM", 5*time.Second, func() bool { return rs[l].LastIndex() == s })
	addX := rs[l].AddVoter(id(x), inproc.Addr(x), 0, 0)
	waitFor(t, "L to append AddVoter X (C2) at S+1", 5*time.Second, func() bool { return rs[l].LastIndex() == s+1 })
	if c := configOf(l); !hasServer(c, x) {
		t.Fatalf("step did not happen: L's latest configuration lacks X: %v", servers(c))
	}
	stillLeads(l, termL)

	// 3. F receives p+2..S+1 (commit index p+1); its responses are lost; then its requests are lost again
	setFates(loseRequest, loseResponse, 0)
	waitFor(t, "F to hold S+1", 10*time.Second, func() bool { return rs[f].LastIndex() == s+1 })
	setFates(loseRequest, loseRequest, 0)
	if ci := rs[l].CommitIndex(); ci != q {
		t.Fatalf("step did not happen: L's commit index is %d before A acknowledges, want %d; %s", ci, q, dump())
	}
	if c := configOf(f); !hasServer(c, x) {
		t.Fatalf("step did not happen: F holds C2 at S+1 but its configuration lacks X: %v", servers(c))
	}
	t.Logf("F holds %v, commit index %d, applied %d", logStore(f, q, s+1), rs[f].CommitIndex(), rs[f].AppliedIndex())

	// 4. A receives p+1..S, not S+1: L commits S (with A and X) and takes a snapshot at S
	setFates(deliver, loseRequest, s)
	for k, fu := range futs {
		if err := fu.Error(); err != nil {
			t.Fatalf("step did not happen: L's c%d: %v; %s", k+2, err, dump())
		}
	}
	waitFor(t, "L to apply S", 10*time.Second, func() bool { return rs[l].AppliedIndex() == s })
	stillLeads(l, termL)
	if ci := rs[l].CommitIndex(); ci != s {
		t.Fatalf("step did not happen: L's commit index is %d, want S=%d (C2 at S+1 must not commit yet); %s", ci, s, dump())
	}
	if err := rs[l].Snapshot().Error(); err != nil {
		t.Fatalf("step did not happen: L's snapshot: %v", err)
	}
	if got := snaps[l].Latest(); got != s {
		t.Fatalf("step did not happen: L's snapshot is at %d, want %d", got, s)
	}
	if first, _ := logs[l].FirstIndex(); first <= q {
		t.Fatalf("step did not happen: L's log starts at %d after its snapshot; the schedule needs it compacted past %d", first, q)
	}
	if rs[f].AppliedIndex() >= s || rs[f].CommitIndex() >= s {
		t.Fatalf("step did not happen: F learnt the commitment of S before the snapshot; %s", dump())
	}

	// 5. F's link opens: L sends its snapshot (S, C1); F keeps its log (it holds (S, T1)) with C2 at S+1
	setFates(loseRequest, deliver, 0)
	waitFor(t, "F to install L's snapshot", 10*time.Second, func() bool {
		return snaps[f].Latest() == s && rs[f].AppliedIndex() >= s
	})
	var c2 raft.Log
	if err := logs[f].GetLog(s+1, &c2); err != nil || c2.Type != raft.LogConfiguration ||
		!hasServer(raft.DecodeConfiguration(c2.Data), x) {
		t.Fatalf("step did not happen: F's log does not hold C2 at S+1 after the install (%v); %s", err, dump())
	}
	cf := configOf(f)
	fStale := !hasServer(cf, x)
	t.Logf("F installed the snapshot at %d; F's log store: %v; F's latest configuration: %v", s,
		logStore(f, s, s+1), servers(cf))
	if fStale {
		t.Logf("configuration rule: F's latest configuration %v is not the latest in its log (%v at %d)",
			servers(cf), servers(raft.DecodeConfiguration(c2.Data)), s+1)
	}

	// 6. A's link opens: C2 commits
	setFates(deliver, deliver, 0)
	if err := addX.Error(); err != nil {
		t.Fatalf("step did not happen: AddVoter X: %v; %s", err, dump())
	}
	waitFor(t, "A and F to hold S+1 and C2 to commit", 5*time.Second, func() bool {
		return rs[a].LastIndex() == s+1 && rs[f].LastIndex() == s+1 && rs[l].CommitIndex() == s+1 &&
			rs[x].LastIndex() == s+1
	})
	stillLeads(l, termL)

	// 7. lose L's AppendEntries with entries past S+1 to A and F; L removes A (C3 at S+2) and commits b at S+3
	transports[l].setFilter(func(target int, req *raft.AppendEntriesRequest) fate {
		if (target == a || target == f) && lastEntry(req) > s+1 {
			return loseRequest
		}
		return deliver
	})
	if err := rs[l].RemoveServer(id(a), 0, 0).Error(); err != nil {
		t.Fatalf("step did not happen: RemoveServer A: %v; %s", err, dump())
	}
	if err := rs[l].Apply([]byte("b"), 0).Error(); err != nil {
		t.Fatalf("step did not happen: L's b: %v; %s", err, dump())
	}
	stillLeads(l, termL)
	if rs[l].LastIndex() != s+3 {
		t.Fatalf("step did not happen: L's b is at %d, want S+3=%d", rs[l].LastIndex(), s+3)
	}
	waitFor(t, "L and X to apply b", 5*time.Second, func() bool {
		return rs[l].AppliedIndex() == s+3 && rs[x].AppliedIndex() == s+3
	})
	if rs[a].LastIndex() != s+1 || rs[f].LastIndex() != s+1 {
		t.Fatalf("step did not happen: A or F holds entries past S+1; %s", dump())
	}
	t.Logf("L committed %v", logStore(l, s+1, s+3))

	// 8. {L, X} | {F, A}: F leads with A's vote (two of C1) and commits c with A
	var group [nNet + 1]int
	group[f], group[a] = 1, 1
	ln.partition(group)
	var leader int
	deadline := time.Now().Add(3 * time.Second)
	for time.Now().Before(deadline) {
		if leader = leaderAmong([]int{f, a}, termL); leader != 0 {
			break
		}
		time.Sleep(2 * time.Millisecond)
	}
	switch {
	case leader == 0 && fStale:
		t.Fatalf("step did not happen: F (configuration %v) was not elected in {F, A}; %s", servers(cf), dump())
	case leader == 0:
		t.Logf("no leader in {F, A} within 3 s (F's latest configuration holds X: two of four votes)")
	case leader != f:
		t.Fatalf("step did not happen: S%d leads in {F, A}, not F; %s", leader, dump())
	default:
		termF := rs[f].CurrentTerm()
		t.Logf("F leads term %d in {F, A} with configuration %v", termF, servers(configOf(f)))
		if err := rs[f].Apply([]byte("c"), 0).Error(); err != nil {
			t.Fatalf("step did not happen: F's c: %v; %s", err, dump())
		}
		waitFor(t, "F and A to apply c", 5*time.Second, func() bool {
			return rs[f].AppliedIndex() >= s+3 && rs[a].AppliedIndex() >= s+3
		})
		t.Logf("F committed %v (commit index %d)", logStore(f, s+1, s+3), rs[f].CommitIndex())
	}

	// state-machine safety: no two servers apply different commands at one index
	byIndex := map[uint64]event{}
	evs := rec.all()
	sort.SliceStable(evs, func(i, j int) bool { return evs[i].index < evs[j].index })
	violated := false
	for _, e := range evs {
		if prev, ok := byIndex[e.index]; ok {
			if prev.cmd != e.cmd {
				t.Errorf("state-machine safety violated: at index %d S%d applied %q but S%d applied %q",
					e.index, prev.server, prev.cmd, e.server, e.cmd)
				violated = true
			}
		} else {
			byIndex[e.index] = e
		}
	}
	if violated {
		t.Logf("roles: L=S%d F=S%d A=S%d X=S%d; snapshot at S=%d with C1; C2 (AddVoter X) at S+1; "+
			"C3 (RemoveServer A) at S+2 and b at S+3 committed by L with X", l, f, a, x, s)
	}
}
