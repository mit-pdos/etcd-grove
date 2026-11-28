// Deterministic schedule on the verification fork: a crash inside installSnapshot brings back upstream #721, which
// the fork's fix (hraft-3's 5c0b97e: discard the log unless it holds the snapshot's last entry) closes only for a
// server that does not crash. installSnapshot makes the snapshot durable (sink.Close) first and discards the
// conflicting log only later (DeleteRange, after the FSM's restore); a server that crashes in between restarts with
// the snapshot and its old log, and NewRaft keeps that log as it is: entries below the snapshot's index that
// conflict with the entries the snapshot stands for (an uncommitted suffix of an older term). Raft (Fig. 13): such a
// log is discarded; a restart must not bring it back. Server F (real raft) with peers played by this test: A, G, L,
// M (the configuration {F, A, G, L, M}: quorum 3 of 5).
//
//  1. A, leader of term 2, sends F entries 2-6 of term 2 (STALE-2..6; A's suffix, never committed: A is deposed).
//  2. L, leader of term 3, has committed entries 2-8 of term 3 (with A and M; F and G missed them) and compacted
//     its log; it sends F its snapshot at (8, 3). F does not hold (8, 3), so it is to discard its log.
//  3. F crashes once the snapshot is durable (its sink closed), before the discard, and restarts from its stores:
//     the snapshot at (8, 3), and the log 1, STALE-2..6. Its last entry is the snapshot's (8, 3).
//  4. L is cut off; F's election timer fires and F leads term 4 with the votes of A (log up to (8, 3)) and G (log up
//     to (1, 1)). G rejects F's first AppendEntries; F backs off to G's log and sends it STALE-2.. from its own log
//     (below its snapshot, still in its log store) as entries of F's log, with commit index 8: G commits and applies
//     entries that conflict with the committed entries 2-6 of term 3 (state-machine safety fails).
//
// The test fails when F, after the restart, sends any server an entry at an index the snapshot covers (<= 8) whose
// term is not 3 (no such entry can be in the log of a server holding the snapshot at (8, 3) under Raft's rules).
package repro

import (
	"errors"
	"fmt"
	"io"
	"sync"
	"testing"
	"time"

	"github.com/hashicorp/raft"
)

type fsm struct{}

func (f *fsm) Apply(*raft.Log) interface{}         { return nil }
func (f *fsm) Snapshot() (raft.FSMSnapshot, error) { return nil, errors.New("no") }
func (f *fsm) Restore(r io.ReadCloser) error       { _, err := io.ReadAll(r); _ = r.Close(); return err }

// --- the crash point: a snapshot store whose sinks, as they close, take a copy of F's stores (the crash image)

type image struct {
	logs   *raft.InmemStore
	stable *raft.InmemStore
	snaps  *raft.InmemSnapshotStore
}

type snapStore struct {
	inner  *raft.InmemSnapshotStore
	onSink func(meta raft.SnapshotMeta, data []byte) // called after a sink closed, with its snapshot
}

type sink struct {
	raft.SnapshotSink
	st   *snapStore
	meta raft.SnapshotMeta
	data []byte
}

func (s *sink) Write(p []byte) (int, error) { s.data = append(s.data, p...); return s.SnapshotSink.Write(p) }
func (s *sink) Close() error {
	if err := s.SnapshotSink.Close(); err != nil {
		return err
	}
	if s.st.onSink != nil {
		s.st.onSink(s.meta, s.data)
	}
	return nil
}

func (s *snapStore) Create(version raft.SnapshotVersion, index, term uint64, configuration raft.Configuration,
	configurationIndex uint64, trans raft.Transport) (raft.SnapshotSink, error) {
	k, err := s.inner.Create(version, index, term, configuration, configurationIndex, trans)
	if err != nil {
		return nil, err
	}
	return &sink{SnapshotSink: k, st: s, meta: raft.SnapshotMeta{Version: version, Index: index, Term: term,
		Configuration: configuration, ConfigurationIndex: configurationIndex}}, nil
}
func (s *snapStore) List() ([]*raft.SnapshotMeta, error) { return s.inner.List() }
func (s *snapStore) Open(id string) (*raft.SnapshotMeta, io.ReadCloser, error) {
	return s.inner.Open(id)
}

// crashImage: F's stores now (log entries, term and vote, the snapshot just closed)
func crashImage(t *testing.T, logs, stable *raft.InmemStore, meta raft.SnapshotMeta, data []byte, tr raft.Transport) *image {
	im := &image{logs: raft.NewInmemStore(), stable: raft.NewInmemStore(), snaps: raft.NewInmemSnapshotStore()}
	first, _ := logs.FirstIndex()
	last, _ := logs.LastIndex()
	for i := first; first > 0 && i <= last; i++ {
		var l raft.Log
		if logs.GetLog(i, &l) == nil {
			c := l
			_ = im.logs.StoreLog(&c)
		}
	}
	for _, k := range []string{"CurrentTerm", "LastVoteTerm"} {
		v, _ := stable.GetUint64([]byte(k))
		_ = im.stable.SetUint64([]byte(k), v)
	}
	if v, err := stable.Get([]byte("LastVoteCand")); err == nil {
		_ = im.stable.Set([]byte("LastVoteCand"), v)
	}
	k, err := im.snaps.Create(meta.Version, meta.Index, meta.Term, meta.Configuration, meta.ConfigurationIndex, tr)
	if err != nil {
		t.Fatal(err)
	}
	_, _ = k.Write(data)
	_ = k.Close()
	return im
}

// --- the transport: F's peers

type trans struct {
	mu       sync.Mutex
	consumer chan raft.RPC
	bad      []string // entries F sent at an index <= 8 with a term other than 3
	sentG    bool
}

func (t *trans) Consumer() <-chan raft.RPC                                { return t.consumer }
func (t *trans) LocalAddr() raft.ServerAddress                            { return "F" }
func (t *trans) SetHeartbeatHandler(cb func(raft.RPC))                    {}
func (t *trans) EncodePeer(id raft.ServerID, a raft.ServerAddress) []byte { return []byte(a) }
func (t *trans) DecodePeer(b []byte) raft.ServerAddress                   { return raft.ServerAddress(b) }
func (t *trans) AppendEntriesPipeline(raft.ServerID, raft.ServerAddress) (raft.AppendPipeline, error) {
	return nil, raft.ErrPipelineReplicationNotSupported
}

// AppendEntries from F (leader): A holds (8, 3) and acknowledges from there; G holds only (1, 1); L, M cut off
func (t *trans) AppendEntries(id raft.ServerID, target raft.ServerAddress, a *raft.AppendEntriesRequest, r *raft.AppendEntriesResponse) error {
	time.Sleep(time.Millisecond)
	t.mu.Lock()
	defer t.mu.Unlock()
	for _, e := range a.Entries {
		if e.Index <= 8 && e.Term != 3 {
			t.bad = append(t.bad, fmt.Sprintf("%s: entry (%d, term %d)", target, e.Index, e.Term))
		}
	}
	switch target {
	case "A":
		*r = raft.AppendEntriesResponse{Term: a.Term, LastLog: 8, Success: a.PrevLogEntry >= 8}
	case "G":
		t.sentG = t.sentG || len(a.Entries) > 0
		ok := a.PrevLogEntry <= 1
		*r = raft.AppendEntriesResponse{Term: a.Term, LastLog: 1, Success: ok}
	default:
		return errors.New("peer unreachable")
	}
	return nil
}
func (t *trans) RequestPreVote(id raft.ServerID, target raft.ServerAddress, a *raft.RequestPreVoteRequest, r *raft.RequestPreVoteResponse) error {
	if target != "A" && target != "G" {
		return errors.New("peer unreachable")
	}
	*r = raft.RequestPreVoteResponse{Term: a.Term - 1, Granted: true}
	return nil
}
func (t *trans) RequestVote(id raft.ServerID, target raft.ServerAddress, a *raft.RequestVoteRequest, r *raft.RequestVoteResponse) error {
	if target != "A" && target != "G" {
		return errors.New("peer unreachable")
	}
	// A's log (up to (8, 3)) and G's (up to (1, 1)) are no more up to date than F's last entry, (8, 3)
	*r = raft.RequestVoteResponse{Term: a.Term, Granted: a.LastLogTerm >= 3 && a.LastLogIndex >= 8}
	return nil
}
func (t *trans) InstallSnapshot(raft.ServerID, raft.ServerAddress, *raft.InstallSnapshotRequest, *raft.InstallSnapshotResponse, io.Reader) error {
	return errors.New("not now")
}
func (t *trans) TimeoutNow(raft.ServerID, raft.ServerAddress, *raft.TimeoutNowRequest, *raft.TimeoutNowResponse) error {
	return errors.New("no")
}

func deliver(t *testing.T, tr *trans, cmd interface{}, data io.Reader) raft.RPCResponse {
	resp := make(chan raft.RPCResponse, 1)
	tr.consumer <- raft.RPC{Command: cmd, Reader: data, RespChan: resp}
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

func TestCrashInInstallSnapshotKeepsConflictingLog(t *testing.T) {
	conf := raft.DefaultConfig()
	conf.LocalID = "F"
	conf.HeartbeatTimeout = time.Second
	conf.ElectionTimeout = time.Second
	conf.LeaderLeaseTimeout = time.Second
	conf.CommitTimeout = 5 * time.Millisecond
	conf.MaxAppendEntries = 1
	logs, stable := raft.NewInmemStore(), raft.NewInmemStore()
	snaps := &snapStore{inner: raft.NewInmemSnapshotStore()}
	all := servers("F", "A", "G", "L", "M")
	tr := &trans{consumer: make(chan raft.RPC)}
	if err := raft.BootstrapCluster(conf, logs, stable, snaps, tr, all); err != nil {
		t.Fatal(err)
	}
	r, err := raft.NewRaft(conf, &fsm{}, logs, stable, snaps, tr)
	if err != nil {
		t.Fatal(err)
	}

	// 1. A (term 2): STALE-2..6
	hdrA := raft.RPCHeader{ProtocolVersion: raft.ProtocolVersionMax, ID: []byte("A"), Addr: []byte("A")}
	var es []*raft.Log
	for i := uint64(2); i <= 6; i++ {
		es = append(es, &raft.Log{Index: i, Term: 2, Type: raft.LogCommand, Data: []byte("STALE")})
	}
	rr := deliver(t, tr, &raft.AppendEntriesRequest{RPCHeader: hdrA, Term: 2, Leader: []byte("A"), PrevLogEntry: 1,
		PrevLogTerm: 1, Entries: es, LeaderCommitIndex: 1}, nil)
	if ae, ok := rr.Response.(*raft.AppendEntriesResponse); rr.Error != nil || !ok || !ae.Success {
		t.Fatalf("F did not take A's entries: %v %+v", rr.Error, rr.Response)
	}

	// 2-3. L (term 3): its snapshot at (8, 3); F crashes as the snapshot's sink closes
	var im *image
	snaps.onSink = func(meta raft.SnapshotMeta, data []byte) {
		if im == nil {
			im = crashImage(t, logs, stable, meta, data, tr)
		}
	}
	hdrL := raft.RPCHeader{ProtocolVersion: raft.ProtocolVersionMax, ID: []byte("L"), Addr: []byte("L")}
	snap := []byte("state after L's entries 2-8")
	rr = deliver(t, tr, &raft.InstallSnapshotRequest{RPCHeader: hdrL, SnapshotVersion: raft.SnapshotVersionMax, Term: 3,
		Leader: []byte("L"), LastLogIndex: 8, LastLogTerm: 3, Configuration: raft.EncodeConfiguration(all),
		ConfigurationIndex: 1, Size: int64(len(snap))}, bytesReader(snap))
	if is, ok := rr.Response.(*raft.InstallSnapshotResponse); rr.Error != nil || !ok || !is.Success {
		t.Fatalf("F did not install L's snapshot: %v %+v", rr.Error, rr.Response)
	}
	if im == nil {
		t.Fatal("no crash image")
	}
	_ = r.Shutdown().Error()

	// 4. F restarts from the crash image and leads term 4 with A's and G's votes
	tr2 := &trans{consumer: make(chan raft.RPC)}
	r2, err := raft.NewRaft(conf, &fsm{}, im.logs, im.stable, im.snaps, tr2)
	if err != nil {
		t.Fatal(err)
	}
	defer r2.Shutdown()
	deadline := time.Now().Add(10 * time.Second)
	for r2.State() != raft.Leader && time.Now().Before(deadline) {
		time.Sleep(5 * time.Millisecond)
	}
	if r2.State() != raft.Leader {
		t.Fatalf("F did not become leader after the restart (term %d)", r2.CurrentTerm())
	}
	time.Sleep(300 * time.Millisecond) // F repairs G's log
	tr2.mu.Lock()
	defer tr2.mu.Unlock()
	if len(tr2.bad) > 3 {
		tr2.bad = tr2.bad[:3]
	}
	if len(tr2.bad) > 0 {
		t.Fatalf("F, restarted with its snapshot at (8, 3) and leader of term %d, sent entries below its snapshot "+
			"from the log the install was to discard: %v", r2.CurrentTerm(), tr2.bad)
	}
}

type reader struct {
	b   []byte
	off int
}

func (r *reader) Read(p []byte) (int, error) {
	if r.off >= len(r.b) {
		return 0, io.EOF
	}
	n := copy(p, r.b[r.off:])
	r.off += n
	return n, nil
}

func bytesReader(b []byte) io.Reader { return &reader{b: b} }
