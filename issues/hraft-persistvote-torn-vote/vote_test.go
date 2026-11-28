// A server that crashes while it persists a vote can, after its restart, grant a vote in the same term to the
// candidate of an older vote without checking that candidate's log. persistVote writes the vote's term
// (LastVoteTerm) and its candidate (LastVoteCand) as two separate StableStore writes; a crash between them leaves
// (T, X): the new term with the candidate X of an earlier term's vote. requestVote then takes "LastVoteTerm == T and
// LastVoteCand == X" for a vote it already gave X in T, and grants X's request again with no log comparison.
//
// Server B (real raft, InmemStore underneath) with peers played by this test: A and X (the configuration
// {A, B, X}: quorum 2 of 3).
//
//  1. X, candidate in term 2 (its log (1, 1), as B's), asks for B's vote: granted (LastVoteTerm 2, LastVoteCand X).
//  2. A, leader of term 3, sends B entry e at index 2 with commit index 2: e is committed (A and B hold it, 2 of 3);
//     B applies it. X never receives it.
//  3. A, candidate in term 4 (its log (2, 3)), asks for B's vote; B writes CurrentTerm 4, then LastVoteTerm 4, then
//     LastVoteCand A. The test takes B's stores as a crash leaves them before each of these writes and after the
//     last (every write is atomic and durable when it returns, as raft requires of a StableStore and as
//     raft-boltdb's transactions provide).
//  4. B restarts from each crash image, and X, candidate in term 4 with its log (1, 1), asks for B's vote. B's last
//     entry is (2, 3), newer than X's: Raft (§5.4.1) requires B to refuse. From the image taken between LastVoteTerm
//     and LastVoteCand, (CurrentTerm 4, LastVoteTerm 4, LastVoteCand X), B grants it, and X (with its own vote)
//     leads term 4 without the committed entry e.
//  5. X, leader of term 4, sends B its entry f at index 2 with commit index 2: B replaces e by f and applies f at
//     index 2, where it applied e before the crash (state-machine safety fails).
//
// The test fails when B, restarted from any crash image, grants X's vote, or applies two entries at one index.
package repro

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
)

// --- B's FSM: what it applied at each index, over all its lives

type record struct {
	mu      sync.Mutex
	applied map[uint64][]string // index -> the commands applied there, in order, across restarts
}

func (rc *record) at(i uint64) []string {
	rc.mu.Lock()
	defer rc.mu.Unlock()
	return append([]string(nil), rc.applied[i]...)
}

type fsm struct{ rc *record }

func (f *fsm) Apply(l *raft.Log) interface{} {
	if l.Type == raft.LogCommand {
		f.rc.mu.Lock()
		f.rc.applied[l.Index] = append(f.rc.applied[l.Index], string(l.Data))
		f.rc.mu.Unlock()
	}
	return nil
}
func (f *fsm) Snapshot() (raft.FSMSnapshot, error) { return nil, errors.New("no snapshots") }
func (f *fsm) Restore(r io.ReadCloser) error       { _ = r.Close(); return errors.New("no snapshots") }

// --- B's stable store: every write atomic; while armed, the image before each write is kept

type kv struct {
	b map[string][]byte
	u map[string]uint64
}

func (s kv) clone() kv {
	c := kv{b: map[string][]byte{}, u: map[string]uint64{}}
	for k, v := range s.b {
		c.b[k] = append([]byte(nil), v...)
	}
	for k, v := range s.u {
		c.u[k] = v
	}
	return c
}

type stable struct {
	mu     sync.Mutex
	s      kv
	armed  bool
	images []kv // while armed: the store before each write
	writes []string
}

func newStable(s kv) *stable { return &stable{s: s} }

func (st *stable) write(key string, f func()) {
	st.mu.Lock()
	defer st.mu.Unlock()
	if st.armed {
		st.images = append(st.images, st.s.clone())
		st.writes = append(st.writes, key)
	}
	f()
}
func (st *stable) Set(k, v []byte) error {
	st.write(string(k), func() { st.s.b[string(k)] = append([]byte(nil), v...) })
	return nil
}
func (st *stable) SetUint64(k []byte, v uint64) error {
	st.write(string(k), func() { st.s.u[string(k)] = v })
	return nil
}
func (st *stable) Get(k []byte) ([]byte, error) {
	st.mu.Lock()
	defer st.mu.Unlock()
	v, ok := st.s.b[string(k)]
	if !ok {
		return nil, errors.New("not found")
	}
	return append([]byte(nil), v...), nil
}
func (st *stable) GetUint64(k []byte) (uint64, error) {
	st.mu.Lock()
	defer st.mu.Unlock()
	return st.s.u[string(k)], nil
}
func (st *stable) arm() {
	st.mu.Lock()
	st.armed = true
	st.mu.Unlock()
}
func (st *stable) disarm() []kv {
	st.mu.Lock()
	defer st.mu.Unlock()
	st.armed = false
	return append(st.images, st.s.clone()) // and the image after the last write
}

func (s kv) String() string {
	return fmt.Sprintf("CurrentTerm %d, LastVoteTerm %d, LastVoteCand %q (raw %v)", s.u["CurrentTerm"],
		s.u["LastVoteTerm"], s.b["LastVoteCand"], s.b)
}

func copyLogs(t *testing.T, from *raft.InmemStore) *raft.InmemStore {
	to := raft.NewInmemStore()
	first, _ := from.FirstIndex()
	last, _ := from.LastIndex()
	for i := first; first > 0 && i <= last; i++ {
		var l raft.Log
		if err := from.GetLog(i, &l); err != nil {
			t.Fatal(err)
		}
		c := l
		if err := to.StoreLog(&c); err != nil {
			t.Fatal(err)
		}
	}
	return to
}

// --- B's transport: B only answers (its timers never fire); it sends nothing

type trans struct{ consumer chan raft.RPC }

func (t *trans) Consumer() <-chan raft.RPC                                { return t.consumer }
func (t *trans) LocalAddr() raft.ServerAddress                            { return "B" }
func (t *trans) SetHeartbeatHandler(cb func(raft.RPC))                    {}
func (t *trans) EncodePeer(id raft.ServerID, a raft.ServerAddress) []byte { return []byte(a) }
func (t *trans) DecodePeer(b []byte) raft.ServerAddress                   { return raft.ServerAddress(b) }
func (t *trans) AppendEntriesPipeline(raft.ServerID, raft.ServerAddress) (raft.AppendPipeline, error) {
	return nil, raft.ErrPipelineReplicationNotSupported
}
func (t *trans) AppendEntries(raft.ServerID, raft.ServerAddress, *raft.AppendEntriesRequest, *raft.AppendEntriesResponse) error {
	return errors.New("unreachable")
}
func (t *trans) RequestPreVote(raft.ServerID, raft.ServerAddress, *raft.RequestPreVoteRequest, *raft.RequestPreVoteResponse) error {
	return errors.New("unreachable")
}
func (t *trans) RequestVote(raft.ServerID, raft.ServerAddress, *raft.RequestVoteRequest, *raft.RequestVoteResponse) error {
	return errors.New("unreachable")
}
func (t *trans) InstallSnapshot(raft.ServerID, raft.ServerAddress, *raft.InstallSnapshotRequest, *raft.InstallSnapshotResponse, io.Reader) error {
	return errors.New("unreachable")
}
func (t *trans) TimeoutNow(raft.ServerID, raft.ServerAddress, *raft.TimeoutNowRequest, *raft.TimeoutNowResponse) error {
	return errors.New("unreachable")
}

func deliver(t *testing.T, tr *trans, cmd interface{}) interface{} {
	resp := make(chan raft.RPCResponse, 1)
	tr.consumer <- raft.RPC{Command: cmd, RespChan: resp}
	select {
	case r := <-resp:
		if r.Error != nil {
			t.Fatalf("B answered %T with an error: %v", cmd, r.Error)
		}
		return r.Response
	case <-time.After(5 * time.Second):
		t.Fatalf("B did not answer %T", cmd)
	}
	return nil
}

func hdr(id string) raft.RPCHeader {
	return raft.RPCHeader{ProtocolVersion: raft.ProtocolVersionMax, ID: []byte(id), Addr: []byte(id)}
}

func vote(t *testing.T, tr *trans, cand string, term, lastIdx, lastTerm uint64) bool {
	r := deliver(t, tr, &raft.RequestVoteRequest{RPCHeader: hdr(cand), Term: term, Candidate: []byte(cand),
		LastLogIndex: lastIdx, LastLogTerm: lastTerm})
	return r.(*raft.RequestVoteResponse).Granted
}

func appendEntries(t *testing.T, tr *trans, leader string, term, prev, prevTerm uint64, es []*raft.Log, commit uint64) {
	r := deliver(t, tr, &raft.AppendEntriesRequest{RPCHeader: hdr(leader), Term: term, Leader: []byte(leader),
		PrevLogEntry: prev, PrevLogTerm: prevTerm, Entries: es, LeaderCommitIndex: commit})
	if !r.(*raft.AppendEntriesResponse).Success {
		t.Fatalf("B refused %s's AppendEntries of term %d", leader, term)
	}
}

func waitApplied(t *testing.T, rc *record, i uint64, n int) {
	deadline := time.Now().Add(5 * time.Second)
	for len(rc.at(i)) < n && time.Now().Before(deadline) {
		time.Sleep(time.Millisecond)
	}
	if len(rc.at(i)) < n {
		t.Fatalf("B did not apply index %d (applied there: %v)", i, rc.at(i))
	}
}

func config() *raft.Config {
	conf := raft.DefaultConfig()
	conf.LocalID = "B"
	// B never times out during the test: every step is a message the test delivers
	conf.HeartbeatTimeout = time.Hour
	conf.ElectionTimeout = time.Hour
	conf.LeaderLeaseTimeout = time.Second
	conf.CommitTimeout = 5 * time.Millisecond
	return conf
}

func TestTornVoteGrantsWithoutLogCheck(t *testing.T) {
	conf := config()
	logs, st, snaps := raft.NewInmemStore(), newStable(kv{b: map[string][]byte{}, u: map[string]uint64{}}), raft.NewInmemSnapshotStore()
	tr := &trans{consumer: make(chan raft.RPC)}
	cfg := raft.Configuration{}
	for _, s := range []string{"A", "B", "X"} {
		cfg.Servers = append(cfg.Servers, raft.Server{Suffrage: raft.Voter, ID: raft.ServerID(s), Address: raft.ServerAddress(s)})
	}
	if err := raft.BootstrapCluster(conf, logs, st, snaps, tr, cfg); err != nil {
		t.Fatal(err)
	}
	rc := &record{applied: map[uint64][]string{}}
	r, err := raft.NewRaft(conf, &fsm{rc}, logs, st, snaps, tr)
	if err != nil {
		t.Fatal(err)
	}

	// 1. X's vote in term 2
	if !vote(t, tr, "X", 2, 1, 1) {
		t.Fatal("B refused X's vote in term 2 (logs equal)")
	}
	// 2. A (term 3): e at 2, committed
	appendEntries(t, tr, "A", 3, 1, 1, []*raft.Log{{Index: 2, Term: 3, Type: raft.LogCommand, Data: []byte("e")}}, 2)
	waitApplied(t, rc, 2, 1)
	// 3. A's vote in term 4, with the crash images
	st.arm()
	if !vote(t, tr, "A", 4, 2, 3) {
		t.Fatal("B refused A's vote in term 4 (A's log is B's)")
	}
	images := st.disarm()
	writes := st.writes
	if err := r.Shutdown().Error(); err != nil {
		t.Fatal(err)
	}

	// 4-5. B restarts from each image; X asks for its vote in term 4
	for k, im := range images {
		at := "after the last write"
		if k < len(writes) {
			at = "before writing " + writes[k]
		}
		tr2 := &trans{consumer: make(chan raft.RPC)}
		r2, err := raft.NewRaft(conf, &fsm{rc}, copyLogs(t, logs), newStable(im.clone()), raft.NewInmemSnapshotStore(), tr2)
		if err != nil {
			t.Fatal(err)
		}
		granted := vote(t, tr2, "X", 4, 1, 1)
		if granted {
			t.Errorf("B, crashed %s of its vote for A in term 4 (stable store: %v) and restarted, granted X's vote "+
				"in term 4 though X's last entry (1, 1) is older than B's (2, 3): X leads term 4 with B's vote and its "+
				"own without the committed entry 2", at, im)
			appendEntries(t, tr2, "X", 4, 1, 1, []*raft.Log{{Index: 2, Term: 4, Type: raft.LogCommand, Data: []byte("f")}}, 2)
			waitApplied(t, rc, 2, 2)
			if a := rc.at(2); !bytes.Equal([]byte(a[0]), []byte(a[1])) {
				t.Errorf("state-machine safety violated: B applied %q at index 2, then %q after the restart", a[0], a[1])
			}
		}
		if err := r2.Shutdown().Error(); err != nil {
			t.Fatal(err)
		}
	}
	if len(images) < 2 {
		t.Fatalf("expected B to write its stable store during the vote; images: %v", images)
	}
}
