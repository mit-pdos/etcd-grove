// Deterministic schedule on the verification fork (upstream v1.8.0 and main have the same code; upstream issue #728,
// fix PR #731, both open): a server restarting with RestoreCommittedLogs replays its committed entries into the FSM
// (restoreFromCommittedLogs: processLogs up to the stored commit index, which sets lastApplied) and then scans its
// log for configuration entries only after max(snapshot index, lastApplied), so the configuration entries between
// its snapshot and the stored commit index are never taken: its latest (and committed) configuration falls back to
// the snapshot's. Raft: a server uses the latest configuration in its log. Server F (real raft, RestoreCommittedLogs
// on, upstream's InmemCommitTrackingStore) with peers played by this test: A, B (the first configuration {F, A, B}:
// quorum 2 of 3), X and Y (added).
//
//  1. A, leader of term 2, sends F a command at 2, committed (commit index 2); F applies it and takes a snapshot at 2
//     (its configuration: the first, {F, A, B}, at 1).
//  2. A sends F the configurations {F, A, B, X} at 3 and {F, A, B, X, Y} at 4 (AddVoter X, AddVoter Y) and a command
//     at 5, all committed (commit index 5, staged with the entries in F's log store).
//  3. F crashes (Shutdown) and restarts on the same stores. restoreSnapshot: the snapshot at 2, configuration
//     {F, A, B}; restoreFromCommittedLogs: entries 3-5 replayed, lastApplied 5; the scan starts at 6. F's latest
//     configuration is {F, A, B}, though its log holds {F, A, B, X, Y} at 4 (committed).
//  4. F's election timer fires; it counts votes in {F, A, B} (quorum 2): A grants and F leads term 3. Its no-op
//     (index 6) is acknowledged by A alone, and F commits it: two of the five voters of the configuration in its log.
//     B, X and Y, a majority of {F, A, B, X, Y}, may meanwhile elect one of them in term 3 and commit a different
//     entry at 6 (two leaders in one term; state-machine safety fails).
//
// The test fails when F's configuration after the restart is not the one at index 4 of its log, and (step 4) when F
// commits an entry acknowledged by only F and A.
package repro

import (
	"errors"
	"io"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
)

type fsm struct{}

type fsmSnap struct{}

func (s *fsmSnap) Persist(sink raft.SnapshotSink) error {
	if _, err := sink.Write([]byte("state")); err != nil {
		return err
	}
	return sink.Close()
}
func (s *fsmSnap) Release() {}

func (f *fsm) Apply(*raft.Log) interface{}         { return nil }
func (f *fsm) Snapshot() (raft.FSMSnapshot, error) { return &fsmSnap{}, nil }
func (f *fsm) Restore(r io.ReadCloser) error       { _, err := io.ReadAll(r); _ = r.Close(); return err }

type trans struct {
	mu       sync.Mutex
	consumer chan raft.RPC
	ackedA   uint64 // in F's term: the last index A acknowledged
}

func (t *trans) Consumer() <-chan raft.RPC                                { return t.consumer }
func (t *trans) LocalAddr() raft.ServerAddress                            { return "F" }
func (t *trans) SetHeartbeatHandler(cb func(raft.RPC))                    {}
func (t *trans) EncodePeer(id raft.ServerID, a raft.ServerAddress) []byte { return []byte(a) }
func (t *trans) DecodePeer(b []byte) raft.ServerAddress                   { return raft.ServerAddress(b) }
func (t *trans) AppendEntriesPipeline(raft.ServerID, raft.ServerAddress) (raft.AppendPipeline, error) {
	return nil, raft.ErrPipelineReplicationNotSupported
}

// AppendEntries from F (leader): A holds F's log up to 5 and takes F's entries after it; the others are cut off
func (t *trans) AppendEntries(id raft.ServerID, target raft.ServerAddress, a *raft.AppendEntriesRequest, r *raft.AppendEntriesResponse) error {
	time.Sleep(time.Millisecond)
	if target != "A" {
		return errors.New("peer unreachable")
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	if a.PrevLogEntry > t.ackedA {
		*r = raft.AppendEntriesResponse{Term: a.Term, LastLog: t.ackedA, Success: false}
		return nil
	}
	if n := len(a.Entries); n > 0 {
		t.ackedA = a.Entries[n-1].Index
	}
	*r = raft.AppendEntriesResponse{Term: a.Term, LastLog: t.ackedA, Success: true}
	return nil
}
func (t *trans) RequestPreVote(id raft.ServerID, target raft.ServerAddress, a *raft.RequestPreVoteRequest, r *raft.RequestPreVoteResponse) error {
	if target != "A" {
		return errors.New("peer unreachable")
	}
	*r = raft.RequestPreVoteResponse{Term: a.Term - 1, Granted: true}
	return nil
}
func (t *trans) RequestVote(id raft.ServerID, target raft.ServerAddress, a *raft.RequestVoteRequest, r *raft.RequestVoteResponse) error {
	if target != "A" {
		return errors.New("peer unreachable")
	}
	// A's log (up to (5, 2)) is no more up to date than F's
	*r = raft.RequestVoteResponse{Term: a.Term, Granted: true}
	return nil
}
func (t *trans) InstallSnapshot(raft.ServerID, raft.ServerAddress, *raft.InstallSnapshotRequest, *raft.InstallSnapshotResponse, io.Reader) error {
	return errors.New("no")
}
func (t *trans) TimeoutNow(raft.ServerID, raft.ServerAddress, *raft.TimeoutNowRequest, *raft.TimeoutNowResponse) error {
	return errors.New("no")
}

func deliver(t *testing.T, tr *trans, cmd interface{}) raft.RPCResponse {
	resp := make(chan raft.RPCResponse, 1)
	tr.consumer <- raft.RPC{Command: cmd, RespChan: resp}
	select {
	case r := <-resp:
		return r
	case <-time.After(5 * time.Second):
		t.Fatal("F did not respond")
	}
	return raft.RPCResponse{}
}

func servers(ids ...string) raft.Configuration {
	c := raft.Configuration{}
	for _, s := range ids {
		c.Servers = append(c.Servers, raft.Server{Suffrage: raft.Voter, ID: raft.ServerID(s), Address: raft.ServerAddress(s)})
	}
	return c
}

func appendFromA(t *testing.T, tr *trans, prev uint64, prevTerm uint64, es []*raft.Log, commit uint64) {
	hdr := raft.RPCHeader{ProtocolVersion: raft.ProtocolVersionMax, ID: []byte("A"), Addr: []byte("A")}
	rr := deliver(t, tr, &raft.AppendEntriesRequest{RPCHeader: hdr, Term: 2, Leader: []byte("A"), PrevLogEntry: prev,
		PrevLogTerm: prevTerm, Entries: es, LeaderCommitIndex: commit})
	if ae, ok := rr.Response.(*raft.AppendEntriesResponse); rr.Error != nil || !ok || !ae.Success {
		t.Fatalf("F did not take A's entries: %v %+v", rr.Error, rr.Response)
	}
}

func waitApplied(t *testing.T, r *raft.Raft, idx uint64) {
	deadline := time.Now().Add(5 * time.Second)
	for r.AppliedIndex() < idx && time.Now().Before(deadline) {
		time.Sleep(time.Millisecond)
	}
	if r.AppliedIndex() < idx {
		t.Fatalf("F applied only up to %d, not %d", r.AppliedIndex(), idx)
	}
}

func TestRestoreCommittedLogsDropsConfigurations(t *testing.T) {
	conf := raft.DefaultConfig()
	conf.LocalID = "F"
	conf.HeartbeatTimeout = time.Second
	conf.ElectionTimeout = time.Second
	conf.LeaderLeaseTimeout = time.Second
	conf.CommitTimeout = 5 * time.Millisecond
	conf.RestoreCommittedLogs = true
	logs, stable, snaps := raft.NewInmemCommitTrackingStore(), raft.NewInmemStore(), raft.NewInmemSnapshotStore()
	first := servers("F", "A", "B")
	tr := &trans{consumer: make(chan raft.RPC)}
	if err := raft.BootstrapCluster(conf, logs, stable, snaps, tr, first); err != nil {
		t.Fatal(err)
	}
	r, err := raft.NewRaft(conf, &fsm{}, logs, stable, snaps, tr)
	if err != nil {
		t.Fatal(err)
	}

	// 1. a command at 2, committed; F's snapshot at 2
	appendFromA(t, tr, 1, 1, []*raft.Log{{Index: 2, Term: 2, Type: raft.LogCommand, Data: []byte("c2")}}, 2)
	waitApplied(t, r, 2)
	// (raft's applied index runs ahead of the FSM's: retry until the FSM has applied 2)
	for tries := 0; ; tries++ {
		err := r.Snapshot().Error()
		if err == nil {
			break
		}
		if tries == 100 {
			t.Fatalf("F's snapshot: %v", err)
		}
		time.Sleep(10 * time.Millisecond)
	}

	// 2. {F, A, B, X} at 3, {F, A, B, X, Y} at 4, a command at 5; committed
	all := servers("F", "A", "B", "X", "Y")
	es := []*raft.Log{
		{Index: 3, Term: 2, Type: raft.LogConfiguration, Data: raft.EncodeConfiguration(servers("F", "A", "B", "X"))},
		{Index: 4, Term: 2, Type: raft.LogConfiguration, Data: raft.EncodeConfiguration(all)},
		{Index: 5, Term: 2, Type: raft.LogCommand, Data: []byte("c5")},
	}
	appendFromA(t, tr, 2, 2, es, 5)
	// A's next AppendEntries (no new entries) carries the commit index; F stages it with its next StoreLogs only,
	// so the stored commit index is the one staged with entries 3-5: 5
	waitApplied(t, r, 5)
	if c := r.GetConfiguration().Configuration(); len(c.Servers) != 5 {
		t.Fatalf("F's configuration before the crash: %v", c)
	}

	// 3. F crashes and restarts on the same stores
	if err := r.Shutdown().Error(); err != nil {
		t.Fatal(err)
	}
	tr2 := &trans{consumer: make(chan raft.RPC), ackedA: 5}
	r2, err := raft.NewRaft(conf, &fsm{}, logs, stable, snaps, tr2)
	if err != nil {
		t.Fatal(err)
	}
	defer r2.Shutdown()
	c := r2.GetConfiguration().Configuration()
	if len(c.Servers) != 5 {
		t.Errorf("after the restart F's log holds the configuration {F, A, B, X, Y} at index 4 (committed), but "+
			"F's configuration is %v", c)
	}

	// 4. F leads term 3 with A's vote; its no-op committed with A's acknowledgement alone
	deadline := time.Now().Add(10 * time.Second)
	for r2.State() != raft.Leader && time.Now().Before(deadline) {
		time.Sleep(5 * time.Millisecond)
	}
	if r2.State() != raft.Leader {
		t.Logf("F did not become leader (its configuration %v)", r2.GetConfiguration().Configuration())
		return
	}
	if err := r2.Barrier(2 * time.Second).Error(); err == nil {
		t.Fatalf("F, leader of term %d, committed its no-op and a barrier acknowledged by F and A only; the latest "+
			"configuration in its log, {F, A, B, X, Y}, needs three", r2.CurrentTerm())
	}
}
